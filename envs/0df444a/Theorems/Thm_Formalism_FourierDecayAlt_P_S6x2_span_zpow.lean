-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_span_zpow
-- name    : Formalism.FourierDecayAlt.P.S6x2.span_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:47.562399+00:00
-- url     : https://prove2.me/theorems/8d132402-041d-46ef-8a8a-62e66607fea3
-- title:
--   S6x2: span zpow
-- statement:
--   The S6x2 construction uses the span zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L136-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L136-L151

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem Formalism.FourierDecayAlt.P.S6x2.span_zpow (c : E) (ν : ℤ) (hc : c ∈ dd E ^ ν.natAbs) :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ c * dd E ^ ν ≤ 1 ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ c ≤ dd E ^ ν := by sorry
