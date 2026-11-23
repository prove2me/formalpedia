-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_blk_iff
-- name    : Formalism.FourierDecayAlt.P.G4.lowerUni_blk_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:27.972074+00:00
-- url     : https://prove2.me/theorems/3fd517a8-d659-4db4-b414-757602a21487
-- title:
--   G4: lower Uni blk iff
-- statement:
--   The G4 construction uses the lower Uni blk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L120-L123

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

theorem Formalism.FourierDecayAlt.P.G4.lowerUni_blk_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    IsLowerUni (blk A b a e) ↔ IsLowerUni A ∧ b = 0 ∧ e = 1 := by sorry
