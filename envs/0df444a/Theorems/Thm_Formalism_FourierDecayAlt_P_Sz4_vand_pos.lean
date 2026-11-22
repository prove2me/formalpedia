-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_pos
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:57.666187+00:00
-- url     : https://prove2.me/theorems/cf44aaa4-8931-447b-a41d-b8a4a860a167
-- title:
--   Sz4: vand pos
-- statement:
--   The Sz4 construction uses the vand pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L279-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L279-L284

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

theorem Formalism.FourierDecayAlt.P.Sz4.vand_pos (p : ℕ) (x : ℕ → ℝ) (h : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ p → x j < x i) :
    0 < Vand p x := by sorry
