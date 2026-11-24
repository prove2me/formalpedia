-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_norm_sq_coeff_le_gaussian_growth
-- name    : Formalism.NormUnitaryCountingLemmas.norm_sq_coeff_le_gaussian_growth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:14.574055+00:00
-- url     : https://prove2.me/theorems/45d6c165-fd46-4b51-bc2e-377e496ee3f5
-- title:
--   Norm Unitary Counting Lemmas: norm sq coeff le gaussian growth
-- statement:
--   The Norm Unitary Counting Lemmas construction uses the norm sq coeff le gaussian growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/GaussianCoefficientFactorialBound.lean#L12-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/GaussianCoefficientFactorialBound.lean#L12-L43

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_GaussianCoefficientFactorialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open ExponentialIntegralMeasures

theorem Formalism.NormUnitaryCountingLemmas.norm_sq_coeff_le_gaussian_growth (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (hS : ∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2))
    (e : Fin G → ℕ) :
    ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i ≤ S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by sorry
