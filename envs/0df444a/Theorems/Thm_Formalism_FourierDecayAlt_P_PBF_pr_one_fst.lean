-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_one_fst
-- name    : Formalism.FourierDecayAlt.P.PBF.pr_one_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:16.413465+00:00
-- url     : https://prove2.me/theorems/920fdd2e-7545-41a7-8eab-b37471792786
-- title:
--   PBF: pr one fst
-- statement:
--   The PBF construction uses the pr one fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L14-L14

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

theorem Formalism.FourierDecayAlt.P.PBF.pr_one_fst : (1 : Q.Pr V).1 = 1 := by sorry
