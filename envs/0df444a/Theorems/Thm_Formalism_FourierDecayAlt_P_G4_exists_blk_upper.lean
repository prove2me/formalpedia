-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_exists_blk_upper
-- name    : Formalism.FourierDecayAlt.P.G4.exists_blk_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:22.780781+00:00
-- url     : https://prove2.me/theorems/5d807831-a7d1-4f68-933e-0121d6948a55
-- title:
--   G4: exists blk upper
-- statement:
--   The G4 construction uses the exists blk upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L125-L132

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

theorem Formalism.FourierDecayAlt.P.G4.exists_blk_upper {n : ℕ} {u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : IsUpperUni u) :
    ∃ (u' : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ), IsUpperUni u' ∧ u = blk u' b 0 1 := by sorry
