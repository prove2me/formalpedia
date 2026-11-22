-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_one
-- name    : Formalism.FourierDecayAlt.P.Wd1.ins_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:32.057615+00:00
-- url     : https://prove2.me/theorems/9387ce2b-05c1-4f5a-9af7-c1e793661536
-- title:
--   Wd1: ins one
-- statement:
--   The Wd1 construction uses the ins one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L124-L127

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd1.ins_one (a : S) : ins a (1 : M2 (SlopeTestRemainingChoices S A)) = 1 := by sorry
