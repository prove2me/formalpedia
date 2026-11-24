-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_blockMulVec_add
-- name    : Formalism.FourierDecayAlt.P.PBF.blockMulVec_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:32:58.271073+00:00
-- url     : https://prove2.me/theorems/d5c54ca4-2515-4457-a216-b2ac3c07c974
-- title:
--   PBF: block Mul Vec add
-- statement:
--   The PBF construction uses the block Mul Vec add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L43-L45

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

theorem Formalism.FourierDecayAlt.P.PBF.blockMulVec_add (M : SlopeTestRemainingChoices S (Q.Pr V)) (X Y : Ix S → V) : actP M (X + Y) = actP M X + actP M Y := by sorry
