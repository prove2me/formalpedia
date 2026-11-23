-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_succ_bot
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_succ_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:28.189818+00:00
-- url     : https://prove2.me/theorems/bf1d2506-a819-43cd-8312-5c5c9f5960ba
-- title:
--   Sz4: vand succ bot
-- statement:
--   The Sz4 construction uses the vand succ bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L294-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L294-L305

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

theorem Formalism.FourierDecayAlt.P.Sz4.vand_succ_bot (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = (∏ j ∈ Icc 2 (p + 1), (x 1 - x j)) * Vand p (fun i => x (i + 1)) := by sorry
