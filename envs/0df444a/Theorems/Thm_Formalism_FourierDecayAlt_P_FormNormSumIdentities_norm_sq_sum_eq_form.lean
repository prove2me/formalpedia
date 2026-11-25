-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_norm_sq_sum_eq_form
-- name    : Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sq_sum_eq_form
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:15.033923+00:00
-- url     : https://prove2.me/theorems/c63c9d26-0f47-4dbb-b3aa-ebaacf91676f
-- title:
--   Form Norm Sum Identities: norm sq sum eq form
-- statement:
--   The Form Norm Sum Identities construction uses the norm sq sum eq form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L37-L44

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

theorem Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sq_sum_eq_form (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → V)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = (B (∑ j ∈ J, conj (a j) • y j) (∑ j ∈ J, conj (a j) • y j)).re := by sorry
