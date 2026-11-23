-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_cob_rem_integral
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.cob_rem_integral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:17.065599+00:00
-- url     : https://prove2.me/theorems/f8193a8a-eab5-4acd-9ddb-877b0bd10bb5
-- title:
--   Lem One: cob rem integral
-- statement:
--   The Lem One construction uses the cob rem integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L389-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L389-L398

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.InvariantFactorPaths.G7.LemOne.cob_rem_integral {p : ℕ} {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFl : cob F (lgF K p) = 0)
    (hde : Integral (cob F (g0F K p))) {f : PowerSeries K} (hcob : Integral (cob F f))
    {a : K} (ha : ‖a‖ ≤ 1) (b : K) : Integral (cob F (rem p f a b)) := by sorry
