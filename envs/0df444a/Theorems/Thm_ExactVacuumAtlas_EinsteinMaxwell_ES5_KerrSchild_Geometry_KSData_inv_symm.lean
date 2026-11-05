-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geometry_KSData_inv_symm
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.KSData.inv_symm
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:20.577763+00:00
-- url     : https://prove2.me/theorems/b26e7054-2429-4528-ad78-75bf542a04d8
-- title:
--   The actual background inverse is symmetric
-- statement:
--   The actual background inverse is symmetric.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/KSMetric.lean#L82-L95; SHA-256 fdac39582de8b631a0c693abbc9f5aabb420bcac6608d5d2792fd413b2e8fbbd. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSMetric
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_Transport_Connection
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections (contract2)
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry
variable {b bi : Metric 5} {v : Pt 5 → ℝ} {k : Pt 5 → Fin 5 → ℝ} {U : Set (Pt 5)}
variable (hD : KSData b bi v k U)
include hD

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.KSData.inv_symm {x : Pt 5} (hx : x ∈ U) (i j : Fin 5) : bi i j x = bi j i x := by sorry
