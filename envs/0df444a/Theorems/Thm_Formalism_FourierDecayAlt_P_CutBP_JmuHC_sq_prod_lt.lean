-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_sq_prod_lt
-- name    : Formalism.FourierDecayAlt.P.CutBP.JmuHC.sq_prod_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:32:18.050102+00:00
-- url     : https://prove2.me/theorems/1b90095f-895d-4202-9821-24c3457cfbfd
-- title:
--   Jmu HC: sq prod lt
-- statement:
--   The Jmu HC construction uses the sq prod lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L110-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L110-L131

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
variable {n : ℕ}

theorem Formalism.FourierDecayAlt.P.CutBP.JmuHC.sq_prod_lt (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, g a b := by sorry
