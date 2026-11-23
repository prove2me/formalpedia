-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_exists_blk_lower
-- name    : Formalism.FourierDecayAlt.P.G4.exists_blk_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:12.668335+00:00
-- url     : https://prove2.me/theorems/4d9ac85b-67e6-470f-be88-930d68941aff
-- title:
--   G4: exists blk lower
-- statement:
--   The G4 construction uses the exists blk lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L134-L141

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

theorem Formalism.FourierDecayAlt.P.G4.exists_blk_lower {n : ℕ} {l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hl : IsLowerUni l) :
    ∃ (l' : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ), IsLowerUni l' ∧ l = blk l' 0 a 1 := by sorry
