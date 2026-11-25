-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRateSplit_norm_sum_le_of_gram
-- name    : Formalism.FourierDecayAlt.P.GermRateSplit.norm_sum_le_of_gram
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:08.755906+00:00
-- url     : https://prove2.me/theorems/83306ed6-6abb-4582-bdf7-056a759d087d
-- title:
--   Germ Rate Split: norm sum le of gram
-- statement:
--   The Germ Rate Split construction uses the norm sum le of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfGram.lean#L26-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfGram.lean#L26-L61

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

theorem Formalism.FourierDecayAlt.P.GermRateSplit.norm_sum_le_of_gram {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ P Q, k P Q = ⟪v P, v Q⟫_ℂ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = ∑ i, (c i : ℂ) * ⟪Y i (P l), Y i (P j)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ := by sorry
