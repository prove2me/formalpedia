-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geometry_ricci_contract_diff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.ricci_contract_diff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:56.875425+00:00
-- url     : https://prove2.me/theorems/1e48405b-5e7b-4f32-ba67-dd60b65bae3c
-- title:
--   Contracted connection-difference helper
-- statement:
--   **Contracted connection-difference helper** (derived lemma about the registered `ricci`).
--   `Γ, Γ̄` and `K` are genuinely differentiable at `x`; the symmetry, `Ckk` and trace identities
--   hold on the whole open `U` and are differentiated only there.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/KSRicci.lean#L85-L220; SHA-256 aafee68ecbc6cbecc405990bce4ac1e2aab6836af1a98ba510524447fce6f4ea. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry.ricci_contract_diff (hU : IsOpen U) (hx : x ∈ U)
    (hΓ : ∀ a p q, DifferentiableAt ℝ (Γ a p q) x) (hΓb : ∀ a p q, DifferentiableAt ℝ (Γb a p q) x)
    (hK : ∀ a, DifferentiableAt ℝ (fun y => K y a) x)
    (hsb : ∀ a p q, Γb a p q x = Γb a q p x)
    (hsC : ∀ y ∈ U, ∀ a p q, cdiffOf Γ Γb a p q y = cdiffOf Γ Γb a q p y)
    (hkk : ∀ y ∈ U, ∀ a, ∑ p, ∑ q, cdiffOf Γ Γb a p q y * K y p * K y q = 0)
    (htr : ∀ y ∈ U, ∀ p, ∑ a, cdiffOf Γ Γb a p a y = 0) :
    ∑ p, ∑ q, ricci Γ p q x * K x p * K x q =
      ∑ p, ∑ q, ricci Γb p q x * K x p * K x q
        - 2 * ∑ a, ∑ p, mOf (cdiffOf Γ Γb) K x a p * covD Γb K x a p
        - ∑ a, ∑ p, mOf (cdiffOf Γ Γb) K x a p * mOf (cdiffOf Γ Γb) K x p a := by sorry
