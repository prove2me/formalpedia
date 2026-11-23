-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_mul
-- name    : Formalism.FourierDecayAlt.P.S6x2.idl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:25.51652+00:00
-- url     : https://prove2.me/theorems/2c1fe255-7b99-4d59-b8fd-82137bf27c7e
-- title:
--   S6x2: idl mul
-- statement:
--   The S6x2 construction uses the idl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L392-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L392-L396

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

theorem Formalism.FourierDecayAlt.P.S6x2.idl_mul (g : ℕ) (k ν : ℤ) (hg : 0 < g) :
    idl E g k ν * FractionalIdeal.spanSingleton _ (g : E) = idl E g (k + 1) ν := by sorry
