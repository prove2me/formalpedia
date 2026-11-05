-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII16R_core_L1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.core_L1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:04:24.098249+00:00
-- url     : https://prove2.me/theorems/fe0ba984-6ac8-49b0-9c7a-4b4e39fe42d2
-- title:
--   Abstract first-order core
-- statement:
--   **Abstract first-order core.** Three real functions on `(0, ε)` with classical derivatives up to
--   order two, vanishing real residuals `realPF = realPA = realPC = 0`, and value-level leading
--   asymptotics. Conclusion: right limits of the actual derivatives and the compatibility relation.
--   No derivative limit, derivative bound, `C¹`/`C⁶` extension or formal coefficient recursion is a
--   hypothesis.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII16RFirstOrder.lean#L699-L732; SHA-256 c37ebd91fc832f0ca92cc961a78b3d0265b3e23c4aed113f53001c44db1c66e9. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.core_L1 {h Q J ε f₁ b₁ a₁ C_F C_b C_A : ℝ} {F b A : ℝ → ℝ} (hε : 0 < ε)
    (hF1 : ∀ x ∈ Ioo (0:ℝ) ε, HasDerivAt F (deriv F x) x)
    (hF2 : ∀ x ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv F) (deriv (deriv F) x) x)
    (hb1 : ∀ x ∈ Ioo (0:ℝ) ε, HasDerivAt b (deriv b x) x)
    (hb2 : ∀ x ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv b) (deriv (deriv b) x) x)
    (hA1 : ∀ x ∈ Ioo (0:ℝ) ε, HasDerivAt A (deriv A x) x)
    (hA2 : ∀ x ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv A) (deriv (deriv A) x) x)
    (hPF : ∀ x ∈ Ioo (0:ℝ) ε, realPF h Q J F b A x = 0)
    (hPA : ∀ x ∈ Ioo (0:ℝ) ε, realPA h Q J F b A x = 0)
    (hPC : ∀ x ∈ Ioo (0:ℝ) ε, realPC h Q J F b A x = 0)
    (hvalF : ∀ x ∈ Ioo (0:ℝ) ε, |F x - (1 + f₁ * x)| ≤ C_F * x ^ 2)
    (hvalb : ∀ x ∈ Ioo (0:ℝ) ε, |b x - (1 + b₁ * x)| ≤ C_b * x ^ 2)
    (hvalA : ∀ x ∈ Ioo (0:ℝ) ε, |A x - a₁ * x| ≤ C_A * x ^ 2) :
    Tendsto (deriv F) (𝓝[>] (0:ℝ)) (𝓝 f₁) ∧ Tendsto (deriv b) (𝓝[>] (0:ℝ)) (𝓝 b₁) ∧
      Tendsto (deriv A) (𝓝[>] (0:ℝ)) (𝓝 a₁) ∧ f₁ - 2 * b₁ = h := by sorry
