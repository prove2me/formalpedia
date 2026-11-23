-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_localisation_scaled_ideal_mem_iff
-- name    : Formalism.FourierDecayAlt.P.S6x2.localisation_scaled_ideal_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:29.363783+00:00
-- url     : https://prove2.me/theorems/2c89d25f-61a2-4dd6-b8f7-38eef7e61f4e
-- title:
--   S6x2: localisation scaled ideal mem iff
-- statement:
--   The S6x2 construction uses the localisation scaled ideal mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L305-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L305-L319

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

theorem Formalism.FourierDecayAlt.P.S6x2.localisation_scaled_ideal_mem_iff (g : ℕ) (k : ℤ) (hg : 0 < g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (t : E) :
    t ∈ locAt E P (zsub E (idl E g k 0)) ↔ t / (g : E) ^ k ∈ locAt E P (zsub E 1) := by sorry
