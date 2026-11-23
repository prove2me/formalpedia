-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_char_blk
-- name    : Formalism.FourierDecayAlt.P.G4.char_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:01.362117+00:00
-- url     : https://prove2.me/theorems/f144f734-7e44-4c34-b405-fee4d829838f
-- title:
--   G4: char blk
-- statement:
--   The G4 construction uses the char blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L358-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L358-L363

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4

theorem Formalism.FourierDecayAlt.P.G4.char_blk : ∀ {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ}, IsUpperUni k →
    subSum (blk (wMat n * k⁻¹ * wMat n) 0 0 1) + superSum (blk k 0 0 1) = 0
  := by sorry
