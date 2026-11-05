-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geodesic_sum_pd_one_esMetric
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.sum_pd_one_esMetric
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:11.665177+00:00
-- url     : https://prove2.me/theorems/2b4becf5-c96b-4680-985e-e767565d8d76
-- title:
--   Radial derivative of the frozen contraction (aligned k), from genuine derivatives
-- statement:
--   Radial derivative of the frozen contraction (aligned `k`), from genuine derivatives.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/CoordinateAcceleration.lean#L272-L291; SHA-256 b908ad47b366e1f7c3e1e9f387b2f112cdf3eeb96b6b7a63f3838c7ab394bfc2. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CoordinateAcceleration
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
variable {n : ℕ}
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
variable (B D A H W : ℝ → ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.sum_pd_one_esMetric {x : Pt 5} (hg : ∀ i j, DifferentiableAt ℝ (esMetric B D A H W i j) x)
    {B' D' H' W' : ℝ} (hB : HasDerivAt B B' (x 1)) (hD : HasDerivAt D D' (x 1))
    (hH : HasDerivAt H H' (x 1)) (hW : HasDerivAt W W' (x 1)) (k : Fin 5 → ℝ) (hk2 : k 2 = 0)
    (hk34 : k 3 = k 4) :
    ∑ j, ∑ l, pd 1 (esMetric B D A H W j l) x * k j * k l =
      -B' * k 0 ^ 2 + D' * k 1 ^ 2 + H' * (k 3 - W (x 1) * k 0) ^ 2 -
        2 * H (x 1) * (k 3 - W (x 1) * k 0) * W' * k 0 := by sorry
