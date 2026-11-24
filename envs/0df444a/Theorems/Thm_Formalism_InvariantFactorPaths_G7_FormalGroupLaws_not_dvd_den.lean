-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_not_dvd_den
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.not_dvd_den
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:55.154734+00:00
-- url     : https://prove2.me/theorems/93b7d84e-0c1c-4884-ac85-5e2cdec79015
-- title:
--   Formal Group Laws: not dvd den
-- statement:
--   The Formal Group Laws construction uses the not dvd den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L218-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L218-L236

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

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.not_dvd_den {p : ℕ} [Fact p.Prime] (r : ℚ) (h : ‖(r : ℚ_[p])‖ ≤ 1) : ¬ p ∣ r.den := by sorry
