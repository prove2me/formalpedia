-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_maxwell_combo_core
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_maxwell_combo_core
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:13.622205+00:00
-- url     : https://prove2.me/theorems/5f524be3-d81b-4086-8f5f-0958ae576f54
-- title:
--   Maxwell combination, operator form
-- statement:
--   Maxwell combination, operator form
--
--   For any null frame on the stated open domain and any C^∞ scalar f, without a field equation, write D_A = fdir E A and X = π_B − β − α_B − 2τ, Y = ε_B − ε − ρ_B − 2ρ, A₀ = τ_B + π + 3α − β_B, B₀ = 3γ + γ_B + μ − μ_B. Then (D₂ + X)(D₀ − 2ρ)f − (D₀ + Y)(D₂ − 2τ)f = 2f(2Ψ₁ + D₁κ − D₃σ + A₀σ − B₀κ) + κD₁f − σD₃f. In particular, the last two derivatives of f are outside the factor 2f. Here B-suffixed spin coefficients mean the index-swapped components in the formal statement, not an assumed numerical conjugation rule.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 任意零标架及 C^∞ 标量 f 的 Maxwell 组合算子恒等式，不假设场方程。右端除 2f 乘自旋／曲率括号外，还包含 κD₁f−σD₃f；这两项不能省略。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPMaxwell.lean#L385-L413; SHA-256 8db724b88398b27f6bd9e66bffe3dd4d56351f4e6b454026a2dd888370ee2a5e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Bianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_maxwell_combo_core (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) {f : Pt 4 → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) :
    (fdir E 2 (fun z => fdir E 0 f z - 2 * npRho g gi E Θ z * f z) x
        + (npPiB g gi E Θ x - npBeta g gi E Θ x - npAlphaB g gi E Θ x - 2 * npTau g gi E Θ x)
          * (fdir E 0 f x - 2 * npRho g gi E Θ x * f x))
      - (fdir E 0 (fun z => fdir E 2 f z - 2 * npTau g gi E Θ z * f z) x
        + (npEpsB g gi E Θ x - npEps g gi E Θ x - npRhoB g gi E Θ x - 2 * npRho g gi E Θ x)
          * (fdir E 2 f x - 2 * npTau g gi E Θ x * f x))
      = 2 * f x * (2 * psi1 g gi E x + fdir E 1 (omL g gi E Θ 0 0 2) x - fdir E 3 (omL g gi E Θ 0 2 2) x
          + (npTauB g gi E Θ x + npPi g gi E Θ x + 3 * npAlpha g gi E Θ x - npBetaB g gi E Θ x)
            * npSigma g gi E Θ x
          - (3 * npGamma g gi E Θ x + npGammaB g gi E Θ x + npMu g gi E Θ x - npMuB g gi E Θ x)
            * npKappa g gi E Θ x)
        + npKappa g gi E Θ x * fdir E 1 f x - npSigma g gi E Θ x * fdir E 3 f x := by sorry
