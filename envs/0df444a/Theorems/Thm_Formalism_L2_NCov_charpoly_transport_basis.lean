-- Prove2me | Theorems.Thm_Formalism_L2_NCov_charpoly_transport_basis
-- name    : Formalism.L2.NCov.charpoly_transport_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:27.635533+00:00
-- url     : https://prove2.me/theorems/37b4f9b0-7950-44c9-8354-f4313d51fb0d
-- title:
--   NCov: charpoly transport basis
-- statement:
--   The NCov construction uses the charpoly transport basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean#L25-L36

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

theorem Formalism.L2.NCov.charpoly_transport_basis [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ a, A₂ (ι (b a)) = ι (A₁ (b a))) :
    A₂.charpoly = A₁.charpoly.map σ := by sorry
