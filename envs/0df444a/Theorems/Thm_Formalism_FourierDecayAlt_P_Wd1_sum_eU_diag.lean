-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_sum_eU_diag
-- name    : Formalism.FourierDecayAlt.P.Wd1.sum_eU_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:55.204051+00:00
-- url     : https://prove2.me/theorems/7a2977fc-4887-4ffb-a4a4-4848ad7ad045
-- title:
--   Wd1: sum e U diag
-- statement:
--   The Wd1 construction uses the sum e U diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L59-L72

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

theorem Formalism.FourierDecayAlt.P.Wd1.sum_eU_diag (a : S) : ∑ i, (eU a i i : SlopeTestRemainingChoices S A) = 1 := by sorry
