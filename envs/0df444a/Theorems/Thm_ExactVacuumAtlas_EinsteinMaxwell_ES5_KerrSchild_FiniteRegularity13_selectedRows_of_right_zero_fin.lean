-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_FiniteRegularity13_selectedRows_of_right_zero_fin
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteRegularity13.selectedRows_of_right_zero_fin
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:01:00.78591+00:00
-- url     : https://prove2.me/theorems/06bcb41d-7155-4ddb-a55e-3dde6724da05
-- title:
--   Positive-side actual realPM realPA realPC = 0 of a C⁶ extension ⇒ the eight VII-04
--   SelectedRows of jet4 F, jet4 b, jet4 A (rows are derived, never assumed)
-- statement:
--   Positive-side actual `realPM realPA realPC = 0` of a `C⁶` extension ⇒ the eight VII-04
--   `SelectedRows` of `jet4 F, jet4 b, jet4 A` (rows are derived, never assumed).
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/FiniteTaylor6.lean#L276-L299; SHA-256 1574b720aae4fb108971020ff42533e011e4a1efaae57f279ab299e3acbe0a6a. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedResiduals
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylor6
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylorJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII13FiniteBranchSpec
open scoped ContDiff Topology
open Polynomial Filter
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII13FiniteBranchSpec
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteRegularity13
set_option autoImplicit false
variable {ε h Q J : ℝ} {F b A : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteRegularity13.selectedRows_of_right_zero_fin (hε : 0 < ε)
    (cF : ContDiffOn ℝ 6 F (Set.Ioo (-ε) ε)) (cb : ContDiffOn ℝ 6 b (Set.Ioo (-ε) ε))
    (cA : ContDiffOn ℝ 6 A (Set.Ioo (-ε) ε))
    (hPM : ∀ x ∈ Set.Ioo 0 ε, realPM h Q J F b A x = 0)
    (hPA : ∀ x ∈ Set.Ioo 0 ε, realPA h Q J F b A x = 0)
    (hPC : ∀ x ∈ Set.Ioo 0 ε, realPC h Q J F b A x = 0) :
    SelectedRows h Q J (jet4 F) (jet4 b) (jet4 A) := by sorry
