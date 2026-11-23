-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_transpose
-- name    : Formalism.FourierDecayAlt.P.G4.blk_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:32.312147+00:00
-- url     : https://prove2.me/theorems/6334709e-e064-41c6-965a-db241996e95a
-- title:
--   G4: blk transpose
-- statement:
--   The G4 construction uses the blk transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L88-L93

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

theorem Formalism.FourierDecayAlt.P.G4.blk_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    (blk A b a e)ᵀ = blk Aᵀ a b e := by sorry
