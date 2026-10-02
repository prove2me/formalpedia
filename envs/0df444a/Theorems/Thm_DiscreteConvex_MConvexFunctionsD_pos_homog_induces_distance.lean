-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_pos_homog_induces_distance
-- name    : DiscreteConvex.MConvexFunctionsD.pos_homog_induces_distance
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:58:50.69988+00:00
-- url     : https://prove2.me/theorems/b3631673-0382-4021-8966-b105f4ac6c5b
-- title:
--   Proposition 6.57 -- pos_homog_induces_distance
-- statement:
--   **Proposition 6.57** (p.164). (1) For $f\in 0M[\mathbb R\to\mathbb R]$, $\gamma_f\in T[\mathbb R]$ (satisfies the triangle inequality). (2) For $f\in 0M[\mathbb Z\to\mathbb Z]$, $\gamma_f\in T[\mathbb Z]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Proposition 6.57.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Proposition 6.57

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromZ

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.57 (p.183). -/
theorem pos_homog_induces_distance (fR : (V → ℝ) → WithTop ℝ) (hfR : ZeroMR fR)
    (fZ : (V → ℤ) → WithTop ℝ) (hfZ : ZeroMZ fZ) (hfZint : IsIntegerValued fZ) :
    TriangleInequality (InducedGammaFromR fR) ∧
    TriangleInequality (InducedGammaFromZ fZ) ∧ IsIntegerValuedGamma (InducedGammaFromZ fZ) := by sorry

end DiscreteConvex.MConvexFunctionsD
