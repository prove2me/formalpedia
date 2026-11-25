-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_inner_sum_smul
-- name    : Formalism.FourierDecayAlt.P.FormNormSumIdentities.inner_sum_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:17.776719+00:00
-- url     : https://prove2.me/theorems/6db9d714-f631-4159-ad1d-fa4d4b5ea7fa
-- title:
--   Form Norm Sum Identities: inner sum smul
-- statement:
--   The Form Norm Sum Identities construction uses the inner sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormSumLeOfForm.lean#L14-L23

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

theorem Formalism.FourierDecayAlt.P.FormNormSumIdentities.inner_sum_smul (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (J : Finset κ)
    (a : κ → ℂ) (P : κ → ι) :
    ⟪∑ j ∈ J, a j • v (P j), ∑ l ∈ J, a l • v (P l)⟫_ℂ =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * k (P j) (P l) := by sorry
