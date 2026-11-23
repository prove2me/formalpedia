-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_succ_top
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_succ_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:12.688528+00:00
-- url     : https://prove2.me/theorems/a0582a49-3a57-4adf-867b-f525f73a459d
-- title:
--   Sz4: vand succ top
-- statement:
--   The Sz4 construction uses the vand succ top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L286-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L286-L292

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

theorem Formalism.FourierDecayAlt.P.Sz4.vand_succ_top (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = Vand p x * ∏ i ∈ Icc 1 p, (x i - x (p + 1)) := by sorry
