-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_prop_2_21_F_convex_in_w_concave_in_c
-- name    : DiscreteConvex.CombinatorialC.prop_2_21_F_convex_in_w_concave_in_c
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:45:52.410222+00:00
-- url     : https://prove2.me/theorems/d51a1bfc-9d89-493c-b476-5d4f554bfb07
-- title:
--   Proposition 2.21 -- F is convex in w and concave in c
-- statement:
--   $F$ is convex in $w$ and concave in $c$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Proposition 2.21.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Proposition 2.21

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_FVal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, Proposition 2.21, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.21.** `F` is convex in `w` and concave in `c`. `F(w,c)` is the page's function only for `c ≥ 0`: for a capacity with a negative entry no
circulation is feasible and the supremum defining it reads `0` (one loop arc, `w > 0`, capacities
`-1, 1, 0` give `0, w, 0`, which is not concave). -/
theorem prop_2_21_F_convex_in_w_concave_in_c {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] (src dst : A → V) :
    (∀ c0 : A → ℝ, 0 ≤ c0 → ConvexOn ℝ Set.univ (fun w => FVal src dst w c0)) ∧
      (∀ w0 : A → ℝ, ConcaveOn ℝ {c : A → ℝ | 0 ≤ c} (fun c => FVal src dst w0 c)) := by sorry

end DiscreteConvex.CombinatorialC
