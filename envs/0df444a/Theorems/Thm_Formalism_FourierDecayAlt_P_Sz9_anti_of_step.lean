-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_anti_of_step
-- name    : Formalism.FourierDecayAlt.P.Sz9.anti_of_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:29.738334+00:00
-- url     : https://prove2.me/theorems/a4953203-e835-420e-b393-427c506f3fad
-- title:
--   Sz9: anti of step
-- statement:
--   The Sz9 construction uses the anti of step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L42-L53

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
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

theorem Formalism.FourierDecayAlt.P.Sz9.anti_of_step (p : ℕ) (x : ℕ → ℝ) (h : ∀ i, 1 ≤ i → i < p → x (i + 1) < x i) :
    ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s := by sorry
