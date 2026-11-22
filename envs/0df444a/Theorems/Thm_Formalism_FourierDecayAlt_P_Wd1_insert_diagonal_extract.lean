-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract
-- name    : Formalism.FourierDecayAlt.P.Wd1.insert_diagonal_extract
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:43.726166+00:00
-- url     : https://prove2.me/theorems/2adeeea0-776e-4b37-bbd7-adea5c8c071a
-- title:
--   Wd1: insert diagonal extract
-- statement:
--   The Wd1 construction uses the insert diagonal extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L129-L132

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

theorem Formalism.FourierDecayAlt.P.Wd1.insert_diagonal_extract (a : S) (b : SlopeTestRemainingChoices S A) : ins a (d0 b) = b := by sorry
