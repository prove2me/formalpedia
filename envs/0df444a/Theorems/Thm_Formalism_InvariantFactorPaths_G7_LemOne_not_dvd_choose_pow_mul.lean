-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_not_dvd_choose_pow_mul
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.not_dvd_choose_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:41.029941+00:00
-- url     : https://prove2.me/theorems/99165457-5d15-4061-bc3d-1bd57592b8b5
-- title:
--   Lem One: not dvd choose pow mul
-- statement:
--   The Lem One construction uses the not dvd choose pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L16-L35

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

theorem Formalism.InvariantFactorPaths.G7.LemOne.not_dvd_choose_pow_mul {p : ℕ} (hp : p.Prime) (k m : ℕ) (hm : ¬ p ∣ m) :
    ¬ p ∣ (p ^ k * m).choose (p ^ k) := by sorry
