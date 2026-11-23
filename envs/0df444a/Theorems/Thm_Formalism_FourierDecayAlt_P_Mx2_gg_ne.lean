-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_gg_ne
-- name    : Formalism.FourierDecayAlt.P.Mx2.gg_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:48.620805+00:00
-- url     : https://prove2.me/theorems/24dd9fcf-f698-48f6-be82-83c3b1f14fdd
-- title:
--   Mx2: gg ne
-- statement:
--   The Mx2 construction uses the gg ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L129-L133

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx2.gg_ne (TT : ℝ) : (gg TT : Fn r) ≠ 0 := by sorry
