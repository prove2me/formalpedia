-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_order_pow_sub_lin
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.order_pow_sub_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:37.948143+00:00
-- url     : https://prove2.me/theorems/094a856e-1bb4-43d0-8997-5e89d23ec61e
-- title:
--   Lem One: order pow sub lin
-- statement:
--   The Lem One construction uses the order pow sub lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L127-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L127-L148

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.LemOne.order_pow_sub_lin {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (F ^ n - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n).order := by sorry
