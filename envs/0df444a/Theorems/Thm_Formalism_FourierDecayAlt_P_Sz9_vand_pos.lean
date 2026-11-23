-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_vand_pos
-- name    : Formalism.FourierDecayAlt.P.Sz9.vand_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:48.542893+00:00
-- url     : https://prove2.me/theorems/0c3a79cb-222d-4ff4-9514-beab7bc14af2
-- title:
--   Sz9: vand pos
-- statement:
--   The Sz9 construction uses the vand pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L30-L40

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz9.vand_pos (p : ℕ) (x : ℕ → ℝ) (h : ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s) :
    0 < Vand p x := by sorry
