-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_norm_ratCast_le_one
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.norm_ratCast_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:25.097293+00:00
-- url     : https://prove2.me/theorems/af46e544-cf1c-44a9-ad4a-63ef587a3b72
-- title:
--   Formal Group Laws: norm rat Cast le one
-- statement:
--   The Formal Group Laws construction uses the norm rat Cast le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L238-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L238-L262

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.norm_ratCast_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (hnp : ‖(p : K)‖ < 1) (r : ℚ) (hr : ¬ p ∣ r.den) : ‖(r : K)‖ ≤ 1 := by sorry
