-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geometry_ricci_sub_expand
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.ricci_sub_expand
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:30.781871+00:00
-- url     : https://prove2.me/theorems/e681c7eb-0d0c-4381-870c-bd4327f6f02d
-- title:
--   Pointwise expansion of the registered ricci difference (genuine pd linearity)
-- statement:
--   Pointwise expansion of the registered `ricci` difference (genuine `pd` linearity).
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/KSRicci.lean#L51-L74; SHA-256 aafee68ecbc6cbecc405990bce4ac1e2aab6836af1a98ba510524447fce6f4ea. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
variable {Γ Γb : Fin 5 → Fin 5 → Fin 5 → Pt 5 → ℝ} {K : Pt 5 → Fin 5 → ℝ} {U : Set (Pt 5)}
  {x : Pt 5}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.ricci_sub_expand (hΓ : ∀ a p q, DifferentiableAt ℝ (Γ a p q) x)
    (hΓb : ∀ a p q, DifferentiableAt ℝ (Γb a p q) x) (p q : Fin 5) :
    ricci Γ p q x = ricci Γb p q x + ∑ i, pd i (cdiffOf Γ Γb i p q) x
      - ∑ i, pd q (cdiffOf Γ Γb i p i) x + ∑ i, ∑ j, qTerm Γb (cdiffOf Γ Γb) x p q i j := by sorry
