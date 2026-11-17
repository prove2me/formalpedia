-- Prove2me | Theorems.Thm_AvgCaseTI_Supplement_theorem_5_6
-- name    : AvgCaseTI.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:36:30.342974+00:00
-- url     : https://prove2.me/theorems/1d7f4d57-5ede-4b51-9f2e-2bd257b0badd
-- title:
--   Theorem 5.6 — orthogonal tensor isomorphism for odd $q$: $\mathrm{poly}_s(n,\log q)$ time, success $1-(n+1)^{-s}-\delta_{n,q}-\varepsilon_{n,q}$
-- statement:
--   Let $s\ge1$ be an integer. There are a Turing machine $M$ and a degree $k$ such that, on instances $(\mathbb F_q,n,A,B)$ with $q$ odd, $n\ge3$ and $A,B\in T(n\times n\times n,q)$:
--
--   1. **Running time.** On every such instance and every coin string, $M$ halts within $(L+2)^k$ steps, $L$ the input length.
--   2. **Soundness.** On every run the output is either “Fail” or a correct answer: the list of exactly the orthogonal isomorphisms $\mathrm{Isos}(A,B)=\{(Q_1,Q_2,Q_3)\in\mathrm O(n,q)^3:B=(Q_1\otimes Q_2\otimes Q_3)\cdot A\}$, the empty list meaning “not orthogonally isomorphic”.
--   3. **Success probability.** For every map $B=B(A)$, with $A$ uniform and the coins $\omega$ independent of $A$,
--   $$
--   \Pr_{A,\omega}[\text{the run returns a correct answer}]\ \ge\ 1-(n+1)^{-s}-\delta_{n,q}-\varepsilon_{n,q},
--   $$
--   where $\delta_{n,q}=\tfrac12\bigl(q^{-n(n-1)}/(c(q)(1-q^{-n(n-1)}))\bigr)^{1/2}$ and $\varepsilon_{n,q}=\Pr_A[C_{\mathrm O}(\mathcal T_A)\ne\{\pm I_{2n}\}]$.
--   4. **Output size.** On every run that returns a correct answer, $|\mathrm{Isos}(A,B)|\le 2L_s$, where $L_s=24(n+1)^{s+1}$.
--   5. **Uniform rate.** There is a constant $C$ (depending on $s$ only) such that for every odd $q$, every $n\ge3$ and every map $B(\cdot)$, the success probability is at least $1-C\,n^{-s}$.
--
--   The orthogonal restriction of tensor isomorphism thus admits a polynomial-time algorithm that succeeds on all but a $1/\mathrm{poly}(n)$ fraction of first tensors, in contrast with the $1/\Theta(q)$ fractions of Theorems 1.1 and 1.2.
--
--   Differences from the source:
--
--   - reading: "the randomized algorithm described in Sec. 5.1" → for every s ≥ 1 there exist a Mathlib TM2 machine M and a degree k (one machine for all odd q) satisfying all five clauses; reason: every algorithmic statement of this mission is existential over a machine; the TM2 model makes it non-vacuous, and all clauses are about the same machine
--   - reading: "poly_s(n, log q) bit operations on every input and every run" → halts within (L + 2)^k steps on every instance with odd q, n ≥ 3, and every coin string; reason: L = Θ(n³ log q + log n), so poly(L) = poly(n, log q); k depends on s only
--   - encoding: outputs "the complete set of orthogonal isomorphisms", "reports nonisomorphism", or "Fail" → the code [false] for Fail; otherwise a leading true, the list length and the listed triples; correct means the listed triples are exactly Isos(A, B), the empty list meaning nonisomorphic; reason: a machine outputs bits; the code is collision-free and the answer is a set
--   - encoding: Pr_{A,ω} with B = B(A) independent of ω → the average over the q^{n³} arrays A of the fraction of coin strings of the instance (A, B(A)) on which the run returns a correct answer, for every function B; reason: the coin length depends on the instance code length; this average is the joint probability
--   - reading: "1 − O_s(n^{−s}) as n → ∞, uniformly over odd q" → ∃ C, ∀ odd q, ∀ n ≥ 3, ∀ B(·): success ≥ 1 − C·n^{−s}; reason: a threshold in n is absorbed into C since the probability is nonnegative
--   - encoding: F_q given → a presentation (p, f) with p^{deg f} odd, as in the published Theorem 1.1; reason: an algorithm needs an explicit field; every F_q has one
--   - encoding: O(2n, q) and the 2n × 2n tuple T_A → matrices indexed by Fin n ⊕ Fin n; reason: the block structure of Eq. (23); same group
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 5.6, pp.33–34 (PDF pp.35–36)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AvgCaseTI_Halts
import Definitions.Def_AvgCaseTI_cn
import Definitions.Def_AvgCaseTI_Supplement_orthSuccProb
import Definitions.Def_AvgCaseTI_Supplement_deltaOrth
import Definitions.Def_AvgCaseTI_Supplement_epsOrth
import Definitions.Def_AvgCaseTI_Supplement_Ls

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- **Theorem 5.6 (orthogonal tensor isomorphism, `q` odd, `n ≥ 3`).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 5.6, pp.33–34 (PDF pp.35–36): "Let q be odd and n ≥ 3. For every fixed positive
integer s, the randomized algorithm described in Sec. 5.1 uses poly_s(n, log q) bit operations on
every input A, B ∈ T(n×n×n, q) and every run. It outputs the complete set of orthogonal isomorphisms,
correctly reports nonisomorphism, or returns “Fail”. Every output other than “Fail” is correct. For
A uniform and any choice B = B(A) independent of the internal randomness ω,
Pr_{A,ω}[A_s(A, B; ω) returns a correct answer] ≥ 1 − (n + 1)^{−s} − δ_{n,q} − ε_{n,q}. On a successful
run there are at most 2L_s orthogonal isomorphisms. In particular, the success probability is
1 − O_s(n^{−s}) as n → ∞, uniformly over odd q."

For every `s ≥ 1` there are a Turing machine `M` and a degree `k` such that, on instances over a field
of odd order `q` with `n ≥ 3`:
1. on every instance and every coin string, `M` halts within `(L + 2)^k` steps;
2. on every run, the output is "Fail" or a correct answer: the list of exactly the orthogonal
   isomorphisms (empty when there is none);
3. for every map `B = B(A)`, `Pr_{A,ω}[correct answer] ≥ 1 − (n + 1)^{−s} − δ_{n,q} − ε_{n,q}`;
4. on every run that returns a correct answer, `|Isos(A, B)| ≤ 2 L_s`, `L_s = 24 (n + 1)^{s+1}`;
5. there is `C` such that, for every odd `q`, every `n ≥ 3` and every map `B = B(A)`,
   `Pr_{A,ω}[correct answer] ≥ 1 − C n^{−s}`.

**Formalization Note.** "The randomized algorithm described in Sec. 5.1" is read as the existence of a
machine (one per `s`, uniform in `q`); the instance data and code are those of the published
`AlgIsoInstance`/`encodeInstance`, and `poly_s(n, log q) = poly(L)`. -/
theorem theorem_5_6 :
    ∀ s : ℕ, 1 ≤ s →
      ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ k : ℕ,
        (∀ x : AlgIsoInstance, Odd x.P.q → 3 ≤ x.n → Halts M k x) ∧
        (∀ x : AlgIsoInstance, Odd x.P.q → 3 ≤ x.n →
          ∀ (r : Fin (timeBound k x) → Bool) (out : List Bool),
            HMBinPacking.OutputsWithin M (encodeInstance x ++ List.ofFn r) out (timeBound k x) →
              out = failCode ∨ OrthCorrectOut x.P x.A x.B out) ∧
        (∀ P : FieldPres, Odd P.q → ∀ n : ℕ, 3 ≤ n → ∀ Bf : Tensor3 P.F n → Tensor3 P.F n,
          1 - ((n : ℝ) + 1) ^ (-(s : ℤ)) - deltaOrth (P.q : ℝ) n - epsOrth P.F n ≤
            orthSuccProb M k P n Bf) ∧
        (∀ x : AlgIsoInstance, Odd x.P.q → 3 ≤ x.n →
          ∀ (r : Fin (timeBound k x) → Bool) (out : List Bool),
            HMBinPacking.OutputsWithin M (encodeInstance x ++ List.ofFn r) out (timeBound k x) →
              OrthCorrectOut x.P x.A x.B out → (orthIsos x.A x.B).ncard ≤ 2 * Ls x.n s) ∧
        ∃ C : ℝ, ∀ P : FieldPres, Odd P.q → ∀ n : ℕ, 3 ≤ n →
          ∀ Bf : Tensor3 P.F n → Tensor3 P.F n,
            1 - C * (n : ℝ) ^ (-(s : ℤ)) ≤ orthSuccProb M k P n Bf := by sorry

end AvgCaseTI.Supplement
