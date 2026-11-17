-- Prove2me | Theorems.Thm_AvgCaseTI_Supplement_theorem_1_2
-- name    : AvgCaseTI.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:34:33.839203+00:00
-- url     : https://prove2.me/theorems/f0202b9a-d39e-4f66-936f-7464719d3149
-- title:
--   Theorem 1.2 — matrix code conjugacy in randomized $\mathrm{poly}(n,\log q)$ time on a $1/\Theta(q)$ fraction of first codes
-- statement:
--   There are a Turing machine $M$, a degree $k$ and an absolute constant $c>0$ with the following properties.
--
--   1. **Running time.** On every instance — a presented finite field $\mathbb F_q$, a dimension $n$ and two arrays $A,B\in U\otimes U^*\otimes V$, $U\cong V\cong\mathbb F_q^n$, of input length $L$ — and for every coin string, $M$ halts within $(L+2)^k$ steps.
--   2. **Correctness on a $1/\Theta(q)$ fraction.** For every $q$ there is $N_0$ such that for every presentation of a field of order $q$ and every $n\ge N_0$, at least
--   $$
--   \frac{c}{q}\cdot q^{n^3}
--   $$
--   of the $q^{n^3}$ first arrays $A$ are good: for **every** second array $B$, with probability at least $2/3$ over the coins, $M$ outputs whether $A$ and $B$ are conjugate matrix codes, i.e. whether $B_k=\sum_\ell t_{k\ell}SA_\ell S^{-1}$ for some $S,T\in\mathrm{GL}(n,q)$.
--
--   Matrix code conjugacy is Tensor-Isomorphism-complete; previous rigorous average-case algorithms for $n$-dimensional codes in $\mathrm M(n,q)$ take time $q^{O(\sqrt n/\log n)}$ on a $1/\Theta(q)$ fraction, or $q^{O(n)}$ on almost all inputs.
--
--   **Formalization Note** The statement has the quantifier layout of the published Theorem 1.1 (`AvgCaseTI.theorem_1_1`), with the same instance code and budget.
--
--   Differences from the source:
--
--   - reading: "correct for 1/Θ(q) fraction of A" → at least (c/q)·q^{n³} good first arrays, c > 0 absolute; reason: the reading R1 of the published Theorem 1.1: Table 2 treats success fractions as lower bounds; an upper bound on where an existential algorithm succeeds has no content
--   - reading: "poly(n, log q)-time algorithm" → OutputsWithin within (L + 2)^k steps of a Mathlib TM2 machine, L the input length; reason: n³ ≤ L = O(n³ log q + log n), so poly(L) = poly(n, log q); machine models differ polynomially
--   - reading: "randomized … algorithm … correct" → for every B, at least 2/3 of the coin strings give the right bit; the time bound holds for every instance and every coin string; reason: the bounded-error reading of the published Theorem 1.1 (R2); any constant in (1/2, 1) is equivalent by repetition
--   - encoding: F_q given → a presentation (p, f), F = F_p[x]/(f), entries in power-basis coordinates, self-delimiting binary code, coins appended; N₀ chosen per q before the presentation; reason: an algorithm needs an explicit field; every F_q has one (reading R3 of the published Theorem 1.1)
--   - encoding: "isomorphic under the natural action of GL(U) × GL(V)" on U ⊗ U* ⊗ V → invertible S, T with B_k = Σ_l T_{kl} S A_l S^{−1} on frontal slices; reason: the action (S ⊗ S^{−t} ⊗ T) written on slices, Eq. (10) of p.22
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.2, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AvgCaseTI_Halts
import Definitions.Def_AvgCaseTI_Supplement_GoodFirstConj

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- **Theorem 1.2 (matrix code conjugacy in randomized `poly(n, log q)` time on a `1/Θ(q)` fraction of
first codes).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.2, p.5 (PDF p.7): "Fix a prime power q, and let n be sufficiently large depending
on q. Let U ≅ F_q^n and V ≅ F_q^n. There is a randomized poly(n, log q)-time algorithm for matrix code
conjugacy: given A, B ∈ U ⊗ U∗ ⊗ V, decide whether they are isomorphic under the natural action of
GL(U) × GL(V). The algorithm is correct for 1/Θ(q) fraction of A ∈ U ⊗ U∗ ⊗ V."

There are one Turing machine `M`, a degree `k` and an absolute constant `c > 0` such that
1. on every instance (presented field `F_q`, `n`, `A`, `B`) and every coin string, `M` halts within
   `(L + 2)^k` steps, `L` the input length;
2. for every `q` there is `N₀` such that for every presentation of a field of order `q` and every
   `n ≥ N₀`, at least `(c/q)·q^{n³}` of the `q^{n³}` first arrays `A` are good: for **every** second
   array `B`, at least `2/3` of the coin strings make `M` output whether `A` and `B` are conjugate
   matrix codes.

**Formalization Note.** The same readings as the published Theorem 1.1: `1/Θ(q)` is the lower bound
`c/q`, `poly(n, log q) = poly(L)`, the field is given by a presentation. -/
theorem theorem_1_2 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧
      (∀ x : AlgIsoInstance, Halts M k x) ∧
      ∀ q : ℕ, ∃ N₀ : ℕ, ∀ P : FieldPres, P.q = q → ∀ n : ℕ, N₀ ≤ n →
        c / (q : ℝ) * (q : ℝ) ^ (n ^ 3) ≤
          (Nat.card {A : Tensor3 P.F n // GoodFirstConj M k P n A} : ℝ) := by sorry

end AvgCaseTI.Supplement
