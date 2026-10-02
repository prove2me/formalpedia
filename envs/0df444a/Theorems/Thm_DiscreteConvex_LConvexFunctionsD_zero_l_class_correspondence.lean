-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_zero_l_class_correspondence
-- name    : DiscreteConvex.LConvexFunctionsD.zero_l_class_correspondence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:07:22.857153+00:00
-- url     : https://prove2.me/theorems/14ded228-5017-47a7-8832-0a62b198436d
-- title:
--   Proposition 7.37 -- zero_l_class_correspondence
-- statement:
--   **Proposition 7.37** (p.194). (1) $0L[\mathbb Z|\mathbb R\to\mathbb R] = 0L[\mathbb R\to\mathbb R]$. (2) The convex extension of a function in $0L[\mathbb Z\to\mathbb R]$ belongs to $0L[\mathbb R\to\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Proposition 7.37.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Proposition 7.37

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.37 (p.194). The three notions of positive homogeneity for L-convex functions
coincide. -/
theorem zero_l_class_correspondence :
    (∀ g : (V → ℝ) → WithTop ℝ, ZeroLZR g ↔ ZeroLR g) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, ZeroLZ g → ZeroLR (fun p => ConvexClosureVal g p)) := by sorry

end DiscreteConvex.LConvexFunctionsD
