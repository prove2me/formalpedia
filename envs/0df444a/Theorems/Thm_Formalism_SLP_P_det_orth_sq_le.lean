-- Prove2me | Theorems.Thm_Formalism_SLP_P_det_orth_sq_le
-- name    : Formalism.SLP.P.det_orth_sq_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:23.826642+00:00
-- url     : https://prove2.me/theorems/3d7c1b9e-8a9e-4de3-8b3e-5bc864ec2a1e
-- title:
--   P: det orth sq le
-- statement:
--   The P construction uses the det orth sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SesquilinearDeterminantHolds.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SesquilinearDeterminantHolds.lean#L45-L52

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]

theorem Formalism.SLP.P.det_orth_sq_le (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖)
    {m : ℕ} (e : Fin m → V₁) (he : Orthonormal ℂ e) (f : Fin m → V₂) (hf : Orthonormal ℂ f) :
    ‖(Matrix.of fun k l => B (e k) (f l)).det‖ ^ 2 ≤ c ^ (2 * m) := by sorry
