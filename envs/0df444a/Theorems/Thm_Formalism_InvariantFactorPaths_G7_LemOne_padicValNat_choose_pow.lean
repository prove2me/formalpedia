-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_padicValNat_choose_pow
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.padicValNat_choose_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:59.904559+00:00
-- url     : https://prove2.me/theorems/a9b3c80e-0b6d-4dbb-89a6-702260ad4f96
-- title:
--   Lem One: padic Val Nat choose pow
-- statement:
--   The Lem One construction uses the padic Val Nat choose pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L47-L56

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

theorem Formalism.InvariantFactorPaths.G7.LemOne.padicValNat_choose_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    padicValNat p ((p ^ (k + 1)).choose (p ^ k)) = 1 := by sorry
