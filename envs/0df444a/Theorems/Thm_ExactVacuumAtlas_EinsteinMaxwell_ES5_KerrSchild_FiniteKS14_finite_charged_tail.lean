-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_FiniteKS14_finite_charged_tail
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteKS14.finite_charged_tail
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:59.333582+00:00
-- url     : https://prove2.me/theorems/46954970-a377-4af1-82a3-c224f3aa2d1d
-- title:
--   Finite charged tail
-- statement:
--   **Finite charged tail.** Actual `PaperData`, explicit `FactorizedN`, actual `PaperBVP` with
--   constants `Q, J`, the independent finite `FiniteBranch6` and `Q ≠ 0` give `0 < δ ≤ ε` such that on
--   the actual radial tail `R > s + δ⁻¹` one has `R ∈ I` and `f, m, N, alphaSq > 0`.
--   No `J ≠ 0`, no `G = 0`, no Kerr–Schild premise.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/FiniteChargedTail.lean#L111-L140; SHA-256 1965f01f595bf93772003f25d0535d492cfec812070a73a44f2334345c29a351. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylor6
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylorJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII13FiniteBranchSpec
open scoped ContDiff Topology
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII13FiniteBranchSpec (FiniteBranch6)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
set_option autoImplicit false
variable {I : Set ℝ} {f m N w p a F b A : ℝ → ℝ} {s h ε Q J : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.FiniteKS14.finite_charged_tail (hP : PaperData I f m N w p a)
    (hN : FactorizedN I N s h) (hB : PaperBVP I f m N w p a Q J)
    (hS : FiniteBranch6 I s ε f m a F b A) (hQ : Q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ R : ℝ, s + δ⁻¹ < R →
      R ∈ I ∧ 0 < f R ∧ 0 < m R ∧ 0 < N R ∧ 0 < alphaSq f m N w p a R := by sorry
