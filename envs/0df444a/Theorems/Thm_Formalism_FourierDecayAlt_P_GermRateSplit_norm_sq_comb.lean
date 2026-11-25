-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRateSplit_norm_sq_comb
-- name    : Formalism.FourierDecayAlt.P.GermRateSplit.norm_sq_comb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:02.733358+00:00
-- url     : https://prove2.me/theorems/e2d31be1-e866-5a80-8ea5-d8e9280a7156
-- title:
--   Germ Rate Split: norm sq comb
-- statement:
--   The Germ Rate Split construction uses the norm sq comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfGram.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfGram.lean#L8-L17

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRateSplit
open Finset
open scoped ComplexConjugate InnerProductSpace

theorem Formalism.FourierDecayAlt.P.GermRateSplit.norm_sq_comb {κ : Type} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J : Finset κ) (b : κ → ℂ)
    (y : κ → W) :
    ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ J, ∑ l ∈ J, conj (b j) * b l * ⟪y j, y l⟫_ℂ := by sorry
