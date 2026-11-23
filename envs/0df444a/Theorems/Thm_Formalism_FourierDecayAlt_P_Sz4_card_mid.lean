-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_card_mid
-- name    : Formalism.FourierDecayAlt.P.Sz4.card_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:54.614508+00:00
-- url     : https://prove2.me/theorems/bba22965-c451-4f76-9e31-bef968054a2a
-- title:
--   Sz4: card mid
-- statement:
--   The Sz4 construction uses the card mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L484-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L484-L488

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.card_mid (c : Cfg) (hc : c.Ok) : (((Icc 2 (c.k - 1)).card : ℕ) : ℝ) = (c.k : ℝ) - 2 := by sorry
