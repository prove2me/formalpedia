-- Prove2me | Theorems.Thm_Deduction_landau_window_ineq
-- name    : Deduction.landau_window_ineq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:21.818981+00:00
-- url     : https://prove2.me/theorems/e61ecbfe-b00e-475e-955b-699b07ddb20c
-- title:
--   Deduction: landau window ineq
-- statement:
--   The Deduction construction uses the landau window ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindowIneq.lean#L27-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindowIneq.lean#L27-L111

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauKernelMax
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauWindowIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction

theorem Deduction.landau_window_ineq {g R : ℝ → ℝ} (hg : Measurable g) {C₀ : ℝ}
    (hC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u)) {σ θ U V : ℝ} (hσ : 2 < σ) (hθ : θ < σ) (hU : 0 < U)
    (hR : IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U V))
    (hR' : ∀ u ∈ Icc U V, 0 ≤ R u ∧ g u ≤ R u) (k : ℕ) (γ : ℝ) :
    ‖∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖ ≤
      2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U V, R u * Real.exp (-θ * u)) -
        (∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re +
        2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) := by sorry
