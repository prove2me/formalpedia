-- Prove2me | Theorems.Thm_Formalism_L2_NCov_charpoly_transport
-- name    : Formalism.L2.NCov.charpoly_transport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:40.50393+00:00
-- url     : https://prove2.me/theorems/654c6364-c157-4ec2-a60e-abf17fc56377
-- title:
--   NCov: charpoly transport
-- statement:
--   The NCov construction uses the charpoly transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean#L38-L43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Module
variable {K₁ K₂ V₁ V₂ : Type*} [Field K₁] [Field K₂] [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂]
  [Module K₂ V₂]

theorem Formalism.L2.NCov.charpoly_transport [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ x, A₂ (ι x) = ι (A₁ x)) :
    A₂.charpoly = A₁.charpoly.map σ := by sorry
