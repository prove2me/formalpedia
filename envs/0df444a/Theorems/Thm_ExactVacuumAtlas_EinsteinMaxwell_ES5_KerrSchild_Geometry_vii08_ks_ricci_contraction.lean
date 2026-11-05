-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geometry_vii08_ks_ricci_contraction
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.vii08_ks_ricci_contraction
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:38.46523+00:00
-- url     : https://prove2.me/theorems/8d826b99-8942-46d9-905f-dbef10d71ea7
-- title:
--   Main root (VII-08 contracted Ricci identity)
-- statement:
--   **Main root (VII-08 contracted Ricci identity).** Same chart, raw `KSData` on open `U`
--   (non-constant, possibly non-diagonal background; no flatness, signature, `v ≠ 0` or `k ≠ 0`):
--   `Ric_g(k,k) = Ric_b(k,k) − v · b(A,A)` with `A = accel b bi k`, all actual registered objects.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/KSRicci.lean#L315-L333; SHA-256 aafee68ecbc6cbecc405990bce4ac1e2aab6836af1a98ba510524447fce6f4ea. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSConnection
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSMetric
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSRicci
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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.vii08_ks_ricci_contraction (hD : KSData b bi v k U) {x : Pt 5} (hx : x ∈ U) :
    contract2 (ricciOf (ksMetric b v k) (ksInverse bi v k)) x (k x) =
      contract2 (ricciOf b bi) x (k x) - v x * contract2 b x (accel b bi k x) := by sorry
