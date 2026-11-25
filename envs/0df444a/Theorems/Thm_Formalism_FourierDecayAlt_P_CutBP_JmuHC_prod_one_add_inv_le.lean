-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_prod_one_add_inv_le
-- name    : Formalism.FourierDecayAlt.P.CutBP.JmuHC.prod_one_add_inv_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:21.527485+00:00
-- url     : https://prove2.me/theorems/058ebf5c-1dde-492d-a69d-4d767f67c2ac
-- title:
--   Jmu HC: prod one add inv le
-- statement:
--   The Jmu HC construction uses the prod one add inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L8-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset

theorem Formalism.FourierDecayAlt.P.CutBP.JmuHC.prod_one_add_inv_le (D : Finset ℕ) (h0 : 0 ∉ D) : ∏ d ∈ D, (1 + 1 / (d : ℝ)) ≤ D.card + 1 := by sorry
