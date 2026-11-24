-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_exists_not_dvd_choose
-- name    : Formalism.InvariantFactorPaths.G7.LemOne.exists_not_dvd_choose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:47.073867+00:00
-- url     : https://prove2.me/theorems/473cc055-7d35-4678-9155-9594b89bbeaf
-- title:
--   Lem One: exists not dvd choose
-- statement:
--   The Lem One construction uses the exists not dvd choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean#L37-L45

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

theorem Formalism.InvariantFactorPaths.G7.LemOne.exists_not_dvd_choose {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n)
    (hpow : ∀ k, n ≠ p ^ k) : ∃ i, 0 < i ∧ i < n ∧ ¬ p ∣ n.choose i := by sorry
