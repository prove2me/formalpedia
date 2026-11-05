-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII17_actualC6_ks
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII17.actualC6_ks
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:05:42.172228+00:00
-- url     : https://prove2.me/theorems/14b869a3-9d64-47e0-bd6f-9c2bc9c3848d
-- title:
--   Restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch ($QJ \ne 0$)
-- statement:
--   Restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch ($QJ \ne 0$)
--
--   Same data and hypotheses as the finite-regularity theorem, and in addition $J \ne 0$ and $Q \ne 0$ for the actual radial conserved integration constants. Besides the finite $C^6$ branch, the conclusion contains the charged-tail, principal-defect, no-geodesic-congruence and general positive-family outputs, and excludes on the whole tail of the original interior angular chart a smooth Kerr–Schild representation $g = \bar g + v\,\ell \otimes \ell$, $\ell = \bar g(K, \cdot)$, $\bar g(K, K) = 0$, with $K$ everywhere nonzero, smooth and background-pregeodesic, in two cases: (i) the background Ricci contraction along its own $K$ is $\le 0$ throughout the tail; (ii) the background Ricci tensor has pointwise Einstein form $\mathrm{Ric}_{\bar g} = \lambda \bar g$ with $\lambda$ an arbitrary function (in particular flat and Ricci-flat backgrounds). Nonaffine parametrisation is allowed; no alignment of the potential with $K$ is assumed.
--
--   **Scope.** Five-dimensional, $\Lambda = 0$, source-free pure Einstein–Maxwell; equal-magnitude two-angular-momentum radial ansatz; real-factored $N$ and the actual first-order value-asymptotic branch (the paper's Eq. 33 branch; it is not derived here from weaker asymptotic-flatness bounds). $Q$, $J$ are the actual radial conservation constants; their normalisation to total charge and angular momentum follows the source and is not formalised as flux integrals. The Kerr–Schild conclusion concerns representations covering a complete tail of the original chart; it is not a statement that charged rotating black holes do not exist and certifies no horizon or solution. **Attribution.** The physical obstruction appears in Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60); the project contributes the finite-regularity applicability proof on actual solutions and its formal certification; no priority is claimed.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII17Closure.lean#L35-L56; SHA-256 5b76727ea1d3a74e20dbd056e661f9541aa82e43b44c5f1dab701f9934323d51. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII16AsymptoticBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII17Algebra
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII17Analysis
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII17C6Bridge
import Definitions.Def_Atlas_Transport_Connection
open Filter Set Topology
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact (FactorizedN pull pullM)
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
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII17
variable {s h Q J ε : ℝ} {I : Set ℝ} {f m N w p a : ℝ → ℝ} {f₁ b₁ a₁ C_F C_b C_A : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII17.actualC6_ks (hε : 0 < ε) (hP : PaperData I f m N w p a) (hN : FactorizedN I N s h)
    (hB : PaperBVP I f m N w p a Q J) (htail : Set.Ioi (s + ε⁻¹) ⊆ I)
    (hCF : 0 ≤ C_F) (hCb : 0 ≤ C_b) (hCA : 0 ≤ C_A)
    (hvalF : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pull  s f x - (1 + f₁ * x)| ≤ C_F * x ^ 2)
    (hvalb : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pullM s m x - (1 + b₁ * x)| ≤ C_b * x ^ 2)
    (hvalA : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pull  s a x - a₁ * x|       ≤ C_A * x ^ 2)
    (hJ : J ≠ 0) (hQ : Q ≠ 0) :
    ∃ η, 0 < η ∧ η ≤ ε ∧ ∃ Fe be Ae : ℝ → ℝ, FiniteBranch6 I s η f m a Fe be Ae ∧
      ChargedTailOutput I s η f m N w p a ∧ PrincipalDefectOutput I f m N w p a ∧
      NoCongruenceOutput I f m N w ∧ GeneralPositiveFamily I f m N w p a ∧
      (¬ ∃ T : ℝ, NonposBackgroundKSTail I f m N w T) ∧
      (¬ ∃ T : ℝ, EinsteinBackgroundKSTail I f m N w T) := by sorry
