-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_FiniteRegularity13_vii13_compact_obstruction
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteRegularity13.vii13_compact_obstruction
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:02:57.47957+00:00
-- url     : https://prove2.me/theorems/6351c239-12c8-4c75-b495-40b2401874c9
-- title:
--   VII13 root 3
-- statement:
--   **VII13 root 3.** Root 2's inputs plus the extra actual hypothesis `realGamma = 0` on
--   `(0, ε)` ⇒ actual core right-zero, jet-Γ₆,₇,₈ = 0, `J³Q⁵ = 0` and `J = 0 ∨ Q = 0`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/FiniteBranchObstruction.lean#L84-L101; SHA-256 7ade502f55a337196342e389dc15c29f22806a981fd4a03bdd6d0b9f1c3a0826. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
open scoped ContDiff
open Polynomial
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII13FiniteBranchSpec
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteRegularity13
set_option autoImplicit false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteRegularity13.vii13_compact_obstruction {ε h Q J : ℝ} {F b A : ℝ → ℝ} (hε : 0 < ε)
    (cF : ContDiffOn ℝ 6 F (Set.Ioo (-ε) ε))
    (cb : ContDiffOn ℝ 6 b (Set.Ioo (-ε) ε))
    (cA : ContDiffOn ℝ 6 A (Set.Ioo (-ε) ε))
    (F0 : F 0 = 1) (b0 : b 0 = 1) (A0 : A 0 = 0)
    (hPM : ∀ x ∈ Set.Ioo 0 ε, realPM h Q J F b A x = 0)
    (hPA : ∀ x ∈ Set.Ioo 0 ε, realPA h Q J F b A x = 0)
    (hPC : ∀ x ∈ Set.Ioo 0 ε, realPC h Q J F b A x = 0)
    (hΓ : ∀ x ∈ Set.Ioo 0 ε, realGamma h Q J F b A x = 0) :
    CompactFiniteObstructionOutput ε h Q J F b A := by sorry
