-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_norm_sum_le_of_form
-- name    : Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:09.170119+00:00
-- url     : https://prove2.me/theorems/093e104e-c913-5dfb-8956-393cba262776
-- title:
--   Form Norm Sum Identities: norm sum le of form
-- statement:
--   The Form Norm Sum Identities construction uses the norm sum le of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L46-L55

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormNormSumIdentities
open Finset
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form {W : Type*} [SeminormedAddCommGroup W] [Module ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hB : ∀ x, (B x x).re ≤ (Cp * ‖x‖) ^ 2) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → W)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ Cp * ‖∑ j ∈ J, conj (a j) • y j‖ := by sorry
