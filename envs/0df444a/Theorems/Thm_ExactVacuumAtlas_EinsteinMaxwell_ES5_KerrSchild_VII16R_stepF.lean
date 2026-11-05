-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII16R_stepF
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.stepF
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:04:16.000593+00:00
-- url     : https://prove2.me/theorems/e155bfd5-5889-41e0-9d99-aaecae3cddde
-- title:
--   Step F
-- statement:
--   **Step F.** From the real `realPF` and `realPC` residuals (incl. the J-term): `F′ → f₁`.
--   `Z = u·F′/F` has `Z′` equal to an explicit expression of values and `A′` (`e2_core`), which
--   converges once `A′ → a₁` (Step A). Hence `Z` has a limit, `F′ = Z·F/u` has the same limit, and
--   the value bound identifies it as `f₁`. No derivative hypothesis on `F′` is assumed.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII16RFirstOrder.lean#L387-L476; SHA-256 c37ebd91fc832f0ca92cc961a78b3d0265b3e23c4aed113f53001c44db1c66e9. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.stepF {h Q J : ℝ} {F b A : ℝ → ℝ} {f₁ a₁ b₁ C_F C_b C_A δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ x ∈ Ioo (0:ℝ) δ, 1 / 2 ≤ 1 - h * x)
    (hF0 : ∀ x ∈ Ioo (0:ℝ) δ, 0 < F x) (hb0 : ∀ x ∈ Ioo (0:ℝ) δ, 0 < b x)
    (hvalF : ∀ x ∈ Ioo (0:ℝ) δ, |F x - (1 + f₁ * x)| ≤ C_F * x ^ 2)
    (hvalb : ∀ x ∈ Ioo (0:ℝ) δ, |b x - (1 + b₁ * x)| ≤ C_b * x ^ 2)
    (hvalA : ∀ x ∈ Ioo (0:ℝ) δ, |A x - a₁ * x| ≤ C_A * x ^ 2)
    (hF1d : ∀ x ∈ Ioo (0:ℝ) δ, HasDerivAt F (deriv F x) x)
    (hF2d : ∀ x ∈ Ioo (0:ℝ) δ, HasDerivAt (deriv F) (deriv (deriv F) x) x)
    (hresF : ∀ x ∈ Ioo (0:ℝ) δ, realPF h Q J F b A x = 0)
    (hresC : ∀ x ∈ Ioo (0:ℝ) δ, realPC h Q J F b A x = 0)
    (hAlim : Tendsto (deriv A) (𝓝[>] (0:ℝ)) (𝓝 a₁)) :
    Tendsto (deriv F) (𝓝[>] (0:ℝ)) (𝓝 f₁) := by sorry
