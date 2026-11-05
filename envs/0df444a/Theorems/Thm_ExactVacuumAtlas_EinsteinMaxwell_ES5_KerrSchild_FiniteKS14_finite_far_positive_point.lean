-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_FiniteKS14_finite_far_positive_point
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteKS14.finite_far_positive_point
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:28.173847+00:00
-- url     : https://prove2.me/theorems/0d22a9d3-be2b-42c2-8486-55998b3922bd
-- title:
--   Strictly positive background contraction beyond any cutoff, for the given fixed actual
--   gb/gbi/v/K
-- statement:
--   Strictly positive background contraction beyond any cutoff, for the given fixed actual
--   `gb/gbi/v/K`: the same data are restricted to a farther tail beyond `T`, `B` and the charged tail;
--   the nonzero point there is upgraded to `> 0` by the actual null-Ricci SOS, which also gives
--   `misalign > 0` and that `K` lies on neither actual principal line.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/FiniteKSObstruction.lean#L149-L191; SHA-256 cf2b2fb71b3636279b11f01d7f25ef4f9bec6c681f19632424c6468f8c711741. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteKS14.finite_far_positive_point (hP : PaperData I f m N w p a) (hN : FactorizedN I N s h)
    (hB : PaperBVP I f m N w p a Q J) (hS : FiniteBranch6 I s ε f m a F b A)
    (hJ : J ≠ 0) (hQ : Q ≠ 0) {T : ℝ}
    {gb gbi : Metric 5} {v : Pt 5 → ℝ} {K : Pt 5 → Fin 5 → ℝ}
    (hD : KSData gb gbi v K (esDomain I ∩ {x : Pt 5 | T < x 1}))
    (hrep : ∀ i j, Set.EqOn (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w i j)
      (ksMetric gb v K i j) (esDomain I ∩ {x : Pt 5 | T < x 1}))
    (hne : ∀ x ∈ esDomain I ∩ {x : Pt 5 | T < x 1}, K x ≠ 0)
    (hgeo : ∀ x ∈ esDomain I ∩ {x : Pt 5 | T < x 1}, PregeodesicAt gb gbi K x) :
    ∀ B : ℝ, ∃ x ∈ esDomain I ∩ {x : Pt 5 | T < x 1}, B < x 1 ∧
      0 < contract2 (ricciOf gb gbi) x (K x) ∧ 0 < misalign f m N w p a x (K x) ∧
      ¬ ∃ t : ℝ, K x = t • kPlus f m N w p a x ∨ K x = t • kMinus f m N w p a x := by sorry
