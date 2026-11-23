-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mulVec_apply
-- name    : Formalism.FourierDecayAlt.P.G2.wMat_mulVec_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:59.248593+00:00
-- url     : https://prove2.me/theorems/3f9ae91b-148c-4b5f-b3d5-a5ba5e5697bb
-- title:
--   G2: w Mat mul Vec apply
-- statement:
--   The G2 construction uses the w Mat mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L77-L78

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G2.wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by sorry
