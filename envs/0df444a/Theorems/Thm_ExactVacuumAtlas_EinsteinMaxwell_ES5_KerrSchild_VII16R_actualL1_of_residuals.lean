-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII16R_actualL1_of_residuals
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.actualL1_of_residuals
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:04:19.844474+00:00
-- url     : https://prove2.me/theorems/bcf033e4-d80f-40f1-b83d-810baa769e3e
-- title:
--   VII16R main theorem (§1 signature, unchanged)
-- statement:
--   **VII16R main theorem (§1 signature, unchanged).** For the actual positive-side pull-backs of the
--   paper's EM data on the real-root branch, value-level leading asymptotics alone give the right limits
--   of the actual derivatives `F′ → f₁`, `b′ → b₁`, `A′ → a₁`, and the compatibility `f₁ − 2b₁ = h`.
--   The residuals are derived from `PaperBVP` (not assumed); the `deriv`s are classical (H0).
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII16RFirstOrder.lean#L735-L769; SHA-256 c37ebd91fc832f0ca92cc961a78b3d0265b3e23c4aed113f53001c44db1c66e9. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open Filter Set Topology
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open Filter Set Topology ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.actualL1_of_residuals
    {s h Q J ε : ℝ} (hε : 0 < ε)
    {I : Set ℝ} {f m N w p a : ℝ → ℝ}
    (hP : PaperData I f m N w p a)
    (hN : FactorizedN I N s h)
    (hB : PaperBVP I f m N w p a Q J)
    (htail : Set.Ioi (s + ε⁻¹) ⊆ I)
    {f₁ b₁ a₁ C_F C_b C_A : ℝ}
    (_hCF : 0 ≤ C_F) (_hCb : 0 ≤ C_b) (_hCA : 0 ≤ C_A)
    (hvalF : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pull  s f x - (1 + f₁ * x)| ≤ C_F * x ^ 2)
    (hvalb : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pullM s m x - (1 + b₁ * x)| ≤ C_b * x ^ 2)
    (hvalA : ∀ x ∈ Set.Ioo (0:ℝ) ε, |pull  s a x - a₁ * x|       ≤ C_A * x ^ 2) :
    Tendsto (deriv (pull  s f)) (𝓝[>] (0:ℝ)) (𝓝 f₁) ∧
    Tendsto (deriv (pullM s m)) (𝓝[>] (0:ℝ)) (𝓝 b₁) ∧
    Tendsto (deriv (pull  s a)) (𝓝[>] (0:ℝ)) (𝓝 a₁) ∧
    f₁ - 2 * b₁ = h := by sorry
