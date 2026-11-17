-- Prove2me | Theorems.Thm_AvgCaseTI_Supplement_theorem_1_3
-- name    : AvgCaseTI.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:35:42.517208+00:00
-- url     : https://prove2.me/theorems/a67d2b3e-2041-4e2d-9318-82e42f2e4358
-- title:
--   Theorem 1.3 — 4-tensor isomorphism in randomized $\mathrm{poly}(n,q)$ time on a $1/\mathrm{poly}(q)$ fraction
-- statement:
--   There are a Turing machine $M$, a degree $k$ and constants $c>0$, $d\in\mathbb N$ (independent of $q$) with the following properties.
--
--   1. **Running time.** On every instance — a presented finite field $\mathbb F_q$, a dimension $n$ and two 4-way arrays $A,B\in U\otimes V\otimes W\otimes X$, $U,V,W,X\cong\mathbb F_q^n$, of input length $L$ — and for every coin string, $M$ halts within $(L+q+2)^k$ steps, a bound polynomial in $n$ and $q$.
--   2. **Correctness on a $1/\mathrm{poly}(q)$ fraction.** For every $q$ there is $N_0$ such that for every presentation of a field of order $q$ and every $n\ge N_0$, at least
--   $$
--   c\,q^{-d}\cdot q^{n^4}
--   $$
--   of the $q^{n^4}$ first arrays $A$ are good: for **every** second array $B$, with probability at least $2/3$ over the coins, $M$ outputs whether there are $L,R,S,T\in\mathrm{GL}(n,q)$ with $B=(L\otimes R\otimes S\otimes T)\cdot A$.
--
--   4-tensor isomorphism subsumes and reduces to 3-tensor isomorphism; the result shows that a polynomial-time average-case algorithm exists for it on a fraction of inputs depending only on $q$.
--
--   Differences from the source:
--
--   - reading: "correct for a 1/poly(q)-fraction of A" → at least c·q^{−d}·q^{n⁴} good first arrays, with c > 0 and d ∈ ℕ independent of q; reason: 1/poly(q) means at least 1/p(q) for a polynomial p, and for q ≥ 2 this is equivalent to c·q^{−d}; the proof (p.28) gives q^{−9}/1024
--   - reading: "poly(n, q)-time algorithm" → OutputsWithin within (L + q + 2)^k steps, L the input length; reason: n ≤ L = O(n⁴ log q + log n), so the bounds (L + q + 2)^k are exactly poly(n, q)
--   - reading: "randomized … algorithm … correct" → for every B, at least 2/3 of the coin strings give the right bit; the time bound holds for every instance and every coin string; reason: the bounded-error reading of the published Theorem 1.1 (R2); any constant in (1/2, 1) is equivalent by repetition
--   - encoding: F_q given → a presentation (p, f), F = F_p[x]/(f), entries in power-basis coordinates, self-delimiting binary code, coins appended; N₀ chosen per q before the presentation; reason: an algorithm needs an explicit field; every F_q has one (reading R3 of the published Theorem 1.1)
--   - encoding: "isomorphism problem of U ⊗ V ⊗ W ⊗ X" → invertible L, R, S, T with B = (L ⊗ R ⊗ S ⊗ T)·A entrywise; reason: the four-factor form of the §2.3 action, as on p.25
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_AvgCaseTI_Supplement_Halts4
import Definitions.Def_AvgCaseTI_Supplement_GoodFirst4

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- **Theorem 1.3 (4-tensor isomorphism in randomized `poly(n, q)` time on a `1/poly(q)` fraction of
first tensors).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8): "Fix a prime power q, and let n be sufficiently large depending
on q. Let U, V, W, X ≅ F_q^n. There is a randomized poly(n, q)-time algorithm for the isomorphism
problem of U ⊗ V ⊗ W ⊗ X, such that the algorithm is correct for a 1/poly(q)-fraction of
A ∈ U ⊗ V ⊗ W ⊗ X."

There are one Turing machine `M`, a degree `k` and absolute constants `c > 0`, `d ∈ ℕ` such that
1. on every instance (presented field `F_q`, `n`, 4-way arrays `A`, `B`) and every coin string, `M`
   halts within `(L + q + 2)^k` steps, `L` the input length;
2. for every `q` there is `N₀` such that for every presentation of a field of order `q` and every
   `n ≥ N₀`, at least `c·q^{−d}·q^{n⁴}` of the `q^{n⁴}` first arrays `A` are good: for **every** second
   array `B`, at least `2/3` of the coin strings make `M` output whether `A` and `B` are isomorphic
   under `GL(n, q)^4`.

**Formalization Note.** `1/poly(q)` is read as the lower bound `c·q^{−d}` with `c, d` independent of
`q`; `(L + q + 2)^k` is `poly(n, q)`. -/
theorem theorem_1_3 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ,
      (∀ x : Instance4, Halts4 M k x) ∧
      ∀ q : ℕ, ∃ N₀ : ℕ, ∀ P : FieldPres, P.q = q → ∀ n : ℕ, N₀ ≤ n →
        c * (q : ℝ) ^ (-(d : ℤ)) * (q : ℝ) ^ (n ^ 4) ≤
          (Nat.card {A : Tensor4 P.F n // GoodFirst4 M k P n A} : ℝ) := by sorry

end AvgCaseTI.Supplement
