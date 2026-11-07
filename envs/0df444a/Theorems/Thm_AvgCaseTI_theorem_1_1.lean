-- Prove2me | Theorems.Thm_AvgCaseTI_theorem_1_1
-- name    : AvgCaseTI.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:44.468382+00:00
-- url     : https://prove2.me/theorems/a611b4c2-4824-4e5f-9a37-36eb6852c496
-- title:
--   Theorem 1.1 — algebra isomorphism in randomized $\mathrm{poly}(n,\log q)$ time on a $1/\Theta(q)$ fraction of first algebras
-- statement:
--   There are a Turing machine $M$, a degree $k$ and an absolute constant $c>0$ with the following properties.
--   1. **Running time.** On every instance — a presented finite field $\mathbb F_q$, a dimension $n$ and two structure tensors $A,B\in T(n\times n\times n,q)$, of input length $L$ — and for every coin string, $M$ halts within $(L+2)^k$ steps.
--   2. **Correctness on a $1/\Theta(q)$ fraction.** For every $q$ there is $N_0$ such that for every presentation of a field $\mathbb F_q$ of order $q$ and every $n\ge N_0$, at least
--   $$
--   \frac{c}{q}\cdot q^{n^3}
--   $$
--   of the $q^{n^3}$ first tensors $A$ are good: for **every** second tensor $B$, with probability at least $2/3$ over the coins, $M$ outputs whether $A$ and $B$ are isomorphic algebras (isomorphic under the natural action of $\mathrm{GL}(U)$ on $U\otimes U\otimes U^*$, $U\cong\mathbb F_q^n$).
--
--   Every earlier rigorous average-case algorithm for this Tensor-Isomorphism-complete problem runs in time $q^{O(n)}$; this one runs in time polynomial in $n$ and $\log q$ on a $1/\Theta(q)$ fraction of the inputs.
--
--   **Formalization Note** The field is part of the input as a presentation $\mathbb F_p[x]/(f)$ and the code lists $p$, $\deg f$, the coefficients of $f$, $n$, and the entries of $A$ and $B$; since $n^3\le L=O(n^3\log q+\log n)$, the bound $(L+2)^k$ is $\mathrm{poly}(n,\log q)$. The coins are a string of length $(L+2)^k$ appended to the input.
--
--   Differences from the source:
--
--   - reading: "correct for 1/Θ(q)-fraction of A" → at least (c/q)·q^{n³} good first tensors, c > 0 absolute; reason: Table 2 (p.7) treats success fractions as lower bounds ("Subsumed by 1/Θ(q)"); an upper bound on where an existential algorithm is correct has no content
--   - reading: "randomized … algorithm … correct" → for every B, at least 2/3 of the coin strings give the right bit; the time bound holds for every coin string and every instance; reason: standard bounded error; any constant in (1/2, 1) is equivalent by repetition (p.21)
--   - reading: "poly(n, log q)-time algorithm" → `OutputsWithin` within (L + 2)^k steps of a Mathlib TM2 machine, L the input length; reason: n³ ≤ L = O(n³ log q + log n), so poly(L) = poly(n, log q); machine models differ polynomially
--   - encoding: F_q given → a presentation (p, f), F = F_p[x]/(f), entries in power-basis coordinates, self-delimiting binary code, coins appended; reason: an algorithm needs an explicit field; every F_q has one; N₀ is chosen per q before the presentation
--   - encoding: "isomorphic under the natural action of GL(U)" → a linear bijection φ with φ(g_A(x, y)) = g_B(φx, φy); reason: the paper's identification B = (T ⊗ T ⊗ T^{−t})·A of p.16
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AvgCaseTI_Halts
import Definitions.Def_AvgCaseTI_GoodFirst

set_option autoImplicit false

namespace AvgCaseTI

/-- **Theorem 1.1 (algebra isomorphism in randomized `poly(n, log q)` time on a `1/Θ(q)` fraction of
first algebras).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.1, p.5
(PDF p.7): "Fix a prime power q, and let n be sufficiently large depending on q. Let U ≅ F_q^n. There
is a randomized poly(n, log q)-time algorithm for algebra isomorphism: given A, B ∈ U ⊗ U ⊗ U∗, decide
whether they are isomorphic under the natural action of GL(U). The algorithm is correct for
1/Θ(q)-fraction of A ∈ U ⊗ U ⊗ U∗."

There are one Turing machine `M`, a degree `k` and an absolute constant `c > 0` such that
1. on every instance (presented field `F_q`, `n`, `A`, `B`) and every coin string, `M` halts within
   `(L + 2)^k` steps, `L` the input length;
2. for every `q` there is `N₀` such that for every presentation of a field of order `q` and every
   `n ≥ N₀`, at least `(c/q)·q^{n³}` of the `q^{n³}` first tensors `A` are good: for **every** second
   tensor `B`, at least `2/3` of the coin strings make `M` output whether `A` and `B` are isomorphic
   algebras.

**Formalization Note.** The field is given by a presentation `(p, f)` (`FieldPres`), encoded with the
instance; `poly(n, log q) = poly(L)` since `n³ ≤ L = O(n³ log q + log n)`. The success fraction
`1/Θ(q)` is read as the lower bound `c/q` (the paper's Table 2, p.7, treats success fractions as lower
bounds). Randomness is a coin string of length `(L + 2)^k` appended to the input. -/
theorem theorem_1_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧
      (∀ x : AlgIsoInstance, Halts M k x) ∧
      ∀ q : ℕ, ∃ N₀ : ℕ, ∀ P : FieldPres, P.q = q → ∀ n : ℕ, N₀ ≤ n →
        c / (q : ℝ) * (q : ℝ) ^ (n ^ 3) ≤
          (Nat.card {A : Tensor3 P.F n // GoodFirst M k P n A} : ℝ) := by sorry

end AvgCaseTI
