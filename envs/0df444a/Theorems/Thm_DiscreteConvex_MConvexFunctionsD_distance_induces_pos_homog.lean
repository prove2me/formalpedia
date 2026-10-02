-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_distance_induces_pos_homog
-- name    : DiscreteConvex.MConvexFunctionsD.distance_induces_pos_homog
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:00:09.589655+00:00
-- url     : https://prove2.me/theorems/ae72e761-0e43-42fd-a483-cb974855d65f
-- title:
--   Proposition 6.58 -- distance_induces_pos_homog
-- statement:
--   **Proposition 6.58** (p.165). (1) For $\gamma\in T[\mathbb R]$, $\hat\gamma\in 0M[\mathbb R\to\mathbb R]$. (2) For $\gamma\in T[\mathbb Z]$, $\hat\gamma_{\mathbb Z}\in 0M[\mathbb Z\to\mathbb Z]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Proposition 6.58.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Proposition 6.58

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_GammaHat

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.58 (p.184). -/
theorem distance_induces_pos_homog (γ : V → V → WithTop ℝ) (hγ : TriangleInequality γ) :
    ZeroMR (GammaHat γ) ∧
    (IsIntegerValuedGamma γ →
      ZeroMZ (fun x : V → ℤ => GammaHat γ (fun v => (x v : ℝ))) ∧
      IsIntegerValued (fun x : V → ℤ => GammaHat γ (fun v => (x v : ℝ)))) := by sorry

end DiscreteConvex.MConvexFunctionsD
