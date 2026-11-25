-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_form_sum_conj
-- name    : Formalism.FourierDecayAlt.P.FormNormSumIdentities.form_sum_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:06.75317+00:00
-- url     : https://prove2.me/theorems/e2f30489-417c-43d0-8fc2-b4a9981684ca
-- title:
--   Form Norm Sum Identities: form sum conj
-- statement:
--   The Form Norm Sum Identities construction uses the form sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L27-L35

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

theorem Formalism.FourierDecayAlt.P.FormNormSumIdentities.form_sum_conj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (y : κ → V) :
    B (∑ j ∈ J, conj (a j) • y j) (∑ l ∈ J, conj (a l) • y l) =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * B (y j) (y l) := by sorry
