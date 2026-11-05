-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_FiniteKS14_finite_tail_G_zero
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteKS14.finite_tail_G_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:48.029278+00:00
-- url     : https://prove2.me/theorems/48e017cd-5a68-4ff2-9091-773b171b439a
-- title:
--   Geometric derivation of G = 0 (inside the contradiction only)
-- statement:
--   **Geometric derivation of `G = 0` (inside the contradiction only).** A congruence on the
--   actual tail `U_T` gives, via the accepted pointwise theorem `vii07_ricci_null_pregeodesic_G_zero`
--   on the actual open charged strip `{s + η⁻¹ < R, 0 < u < 1}` (actual PaperBVP Einstein equations),
--   `G = 0` on the whole radial tail `(s + η⁻¹, ∞)` for a radius `0 < η ≤ ε` with `T < s + η⁻¹`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/FiniteKSObstruction.lean#L53-L83; SHA-256 cf2b2fb71b3636279b11f01d7f25ef4f9bec6c681f19632424c6468f8c711741. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ChargedTail
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedResiduals
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CoordinateAcceleration
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylor6
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylorJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_GeodesicCongruenceObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSBackgroundEnergy
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSConnection
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSMetric
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSRicci
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_NullRicciEnergy
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PrincipalGeodesic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RicciNullDirections
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII13FiniteBranchSpec
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII14FiniteKSSpec
import Definitions.Def_Atlas_Transport_Connection
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact (FactorizedN)
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullEnergy
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.BackgroundEnergy
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII13FiniteBranchSpec (FiniteBranch6)
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII14FiniteKSSpec
open ExactVacuumAtlas.EinsteinMaxwell.D (EMCertificateD)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
set_option autoImplicit false
variable {I : Set ℝ} {f m N w p a F b A : ℝ → ℝ} {s h ε Q J : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteKS14.finite_tail_G_zero (hP : PaperData I f m N w p a) (hN : FactorizedN I N s h)
    (hB : PaperBVP I f m N w p a Q J) (hS : FiniteBranch6 I s ε f m a F b A) (hQ : Q ≠ 0)
    {T : ℝ} {V : Pt 5 → Fin 5 → ℝ}
    (hV : RicciNullPregeodesicField (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
      (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) (esDomain I ∩ {x : Pt 5 | T < x 1}) V) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ T < s + η⁻¹ ∧ ∀ R ∈ Set.Ioi (s + η⁻¹), Gfun p a R = 0 := by sorry
