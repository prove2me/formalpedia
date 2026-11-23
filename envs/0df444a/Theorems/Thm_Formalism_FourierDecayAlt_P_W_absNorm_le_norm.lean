-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_W_absNorm_le_norm
-- name    : Formalism.FourierDecayAlt.P.W.absNorm_le_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:41.502507+00:00
-- url     : https://prove2.me/theorems/d619d854-5ed6-45ac-aa52-d119b3081841
-- title:
--   W: abs Norm le norm
-- statement:
--   The W construction uses the abs Norm le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L159-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L159-L199

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W

theorem Formalism.FourierDecayAlt.P.W.absNorm_le_norm {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by sorry
