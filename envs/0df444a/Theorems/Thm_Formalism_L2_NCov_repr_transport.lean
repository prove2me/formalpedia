-- Prove2me | Theorems.Thm_Formalism_L2_NCov_repr_transport
-- name    : Formalism.L2.NCov.repr_transport
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:46.456822+00:00
-- url     : https://prove2.me/theorems/7f264d37-a2a7-4b25-9c9e-9b433c9748b0
-- title:
--   NCov: repr transport
-- statement:
--   The NCov construction uses the repr transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean#L10-L23

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

theorem Formalism.L2.NCov.repr_transport (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (x : V₁) (r : n) :
    (Module.Basis.mk hli hsp.ge).repr (ι x) r = σ (b.repr x r) := by sorry
