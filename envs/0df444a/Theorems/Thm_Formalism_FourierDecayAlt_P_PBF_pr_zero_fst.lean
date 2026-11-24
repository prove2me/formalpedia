-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_zero_fst
-- name    : Formalism.FourierDecayAlt.P.PBF.pr_zero_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:34:01.440797+00:00
-- url     : https://prove2.me/theorems/58561178-5b64-4312-bf6b-c3035d0d19ed
-- title:
--   PBF: pr zero fst
-- statement:
--   The PBF construction uses the pr zero fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L13-L13

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.PBF.pr_zero_fst : (0 : Q.Pr V).1 = 0 := by sorry
