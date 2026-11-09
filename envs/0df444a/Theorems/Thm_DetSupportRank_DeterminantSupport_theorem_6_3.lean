-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_theorem_6_3
-- name    : DetSupportRank.DeterminantSupport.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:46.996032+00:00
-- url     : https://prove2.me/theorems/73d67b38-d616-497d-bbbb-5c2fa48cdd0f
-- title:
--   Theorem 6.3 — Pawlowski permutation counting bound
-- statement:
--   Let $n\ge3$, let $v\in\mathbb R^n$ have pairwise distinct coordinates and nonzero coordinate sum, and let $0\ne w\in\mathbb R^n$. Then
--   $$|\{\sigma\in S_n:w\cdot v^\sigma=0\}|\le\begin{cases}(n-1)!,&n\text{ odd},\\n(n-2)!,&n\text{ even}.\end{cases}$$
--   The count is over permutations themselves. This is Pawlowski's result as restated by the canonical source, including both parity constants.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 6.3, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Permutations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Theorem 6.3, p.27. -/
theorem theorem_6_3 {n : ℕ} (hn : 3 ≤ n) (v w : Fin n → ℝ)
    (hv : Function.Injective v) (hs : ∑ i, v i ≠ 0) (hw : w ≠ 0) :
    Nat.card {σ : Equiv.Perm (Fin n) // ∑ i, w i * v (σ i) = 0} ≤
      if Odd n then Nat.factorial (n - 1) else n * Nat.factorial (n - 2) := by sorry

end DetSupportRank.DeterminantSupport
