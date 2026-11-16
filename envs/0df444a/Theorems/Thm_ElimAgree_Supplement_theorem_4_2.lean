-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_4_2
-- name    : ElimAgree.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:38:55.086287+00:00
-- url     : https://prove2.me/theorems/5894a8ae-0abc-4439-bab4-a14930b70efc
-- title:
--   Theorem 4.2 (Universal upper bound) — one message of $\min\{n,\lceil\log(2+2^n\ln(1/\alpha)/k)\rceil\}$ bits
-- statement:
--   Let $k\ge1$, let $f_1,\dots,f_k$ be arbitrary Boolean functions in which Bob's input to each instance has length $n\ge1$, and let $0<\alpha<1$. Then
--
--   $$R^{\mathrm{pub},A}_{\alpha2^{-k}}\big(\mathrm{Elim}(f_1,\dots,f_k)\big)\ \le\ \min\Big\{n,\ \Big\lceil\log\Big(2+\frac{2^n\ln(1/\alpha)}k\Big)\Big\rceil\Big\},\tag{4.3}$$
--
--   by a protocol that uses one message from Bob to Alice. The functions need not coincide, and the inputs need not be distinct.
--
--   For $\alpha=1/e$ and $k\le2^n$ the bound is at most $n-\log k+3$; for $k\ge2^n$ it is a constant.
--
--   **Formalization Note** Bob's inputs are $\{0,1\}^n$ as `Fin n → Bool`; Alice's input types are arbitrary. The claim is the existence of a distribution over Bob-only trees of depth at most the bound, with error at most $\alpha2^{-k}$ on every input.
--
--   Differences from the source:
--   - reading: k instances (k ≥ 1 implicit) → 1 ≤ k; reason: the bound divides by k
--   - encoding: R ≤ b by a one-message protocol from Bob to Alice → a PMF over trees with only Bob nodes, depth ≤ b, Alice output, pointwise error ≤ α2^{−k}; reason: same statement
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 4.2, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models

namespace ElimAgree

namespace Supplement

/-- Theorem 4.2 (Universal upper bound), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.17. Suppose Bob's input to each instance has length `n ≥ 1`.
For every `0 < α < 1`, `R^{pub,A}_{α2^{−k}}(Elim(f_1, …, f_k)) ≤ min{n, ⌈log(2 + 2^n ln(1/α)/k)⌉}`
(4.3). The protocol uses one message from Bob to Alice. The functions need not coincide, and the
inputs need not be distinct.

**Formalization Note.** Bob's inputs are `Fin n → Bool`; Alice's input types `X i` and the functions
`f_i` are arbitrary. The claim is the existence of a `PMF` over trees with only Bob's nodes, depth at
most the bound, Alice's output at the leaves, and error at most `α2^{−k}` on every input. -/
theorem theorem_4_2 (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) (X : Fin k → Type)
    (f : ∀ i, X i → (Fin n → Bool) → Bool) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ μ : PMF (AliceProt (∀ i, X i) (Fin k → Fin n → Bool) (Fin k → Bool)),
      (∀ T ∈ μ.support, IsOneWayBA T) ∧
      CostLE μ (min n ⌈Real.logb 2 (2 + 2 ^ n * Real.log (1 / α) / k)⌉₊) ∧
      ∀ x y, aliceErr (elimAns (Y := fun _ => Fin n → Bool) f) μ x y ≤
        ENNReal.ofReal (α / 2 ^ k) := by sorry

end Supplement

end ElimAgree
