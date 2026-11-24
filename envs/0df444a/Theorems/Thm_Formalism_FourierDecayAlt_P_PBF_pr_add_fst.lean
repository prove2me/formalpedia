-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_add_fst
-- name    : Formalism.FourierDecayAlt.P.PBF.pr_add_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:36.915203+00:00
-- url     : https://prove2.me/theorems/a31a35e7-dc0a-4516-916a-e57d1573a030
-- title:
--   PBF: pr add fst
-- statement:
--   The PBF construction uses the pr add fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L11-L11

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

theorem Formalism.FourierDecayAlt.P.PBF.pr_add_fst (p q : Q.Pr V) : (p + q).1 = p.1 + q.1 := by sorry
