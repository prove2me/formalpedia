-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_branchingAlg_of
-- name    : Formalism.FourierDecayAlt.P.qr_branchingAlg_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:08:59.224581+00:00
-- url     : https://prove2.me/theorems/25d6a383-3439-44ee-be5a-61cb98865e48
-- title:
--   P: qr branching Alg of
-- statement:
--   The P construction uses the qr branching Alg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L234-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L234-L243

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.qr_branchingAlg_of : Qr.Decomp → Qr.CapIndep → Qr.IrredCap → Qr.BranchingAlg := by sorry
