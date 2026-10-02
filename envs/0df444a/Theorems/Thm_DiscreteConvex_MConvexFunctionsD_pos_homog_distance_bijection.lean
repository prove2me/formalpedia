-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_pos_homog_distance_bijection
-- name    : DiscreteConvex.MConvexFunctionsD.pos_homog_distance_bijection
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:56:48.406185+00:00
-- url     : https://prove2.me/theorems/36346878-42c9-4e31-9963-386ad905baeb
-- title:
--   Theorem 6.59 -- pos_homog_distance_bijection
-- statement:
--   **Theorem 6.59** (p.165). The mappings $\Phi: f\mapsto\gamma_f$ (Eq. (6.81)) and $\Psi:\gamma\mapsto\hat\gamma$ (Eq. (6.82)) between $0M[\mathbb R\to\mathbb R]$ and $T[\mathbb R]$ are inverse to each other, establishing a one-to-one correspondence. The same holds for $0M[\mathbb Z\to\mathbb Z]$ and $T[\mathbb Z]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Theorem 6.59.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Theorem 6.59

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_GammaHat

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.59 (p.184). -/
theorem pos_homog_distance_bijection (γ : V → V → WithTop ℝ) (hγ : TriangleInequality γ) :
    InducedGammaFromR (GammaHat γ) = γ ∧
    (∀ f : (V → ℝ) → WithTop ℝ, ZeroMR f → GammaHat (InducedGammaFromR f) = f) := by sorry

end DiscreteConvex.MConvexFunctionsD
