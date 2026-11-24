-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_limit_map
-- name    : Formalism.NG.IdemLiftAlt.limit_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:30.566795+00:00
-- url     : https://prove2.me/theorems/3dbe3cc5-3afa-4ec4-a555-dffa52780497
-- title:
--   Idem Lift Alt: limit map
-- statement:
--   The Idem Lift Alt construction uses the limit map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L205-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L205-L217

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
variable [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Module.Finite O A]
omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem Formalism.NG.IdemLiftAlt.limit_map (a L : A) (n : ℕ)
    (hL : ∀ j : ℕ, aeval a (nP (n + j)) - L ∈ IsLocalRing.maximalIdeal O ^ j • (⊤ : Submodule O A))
    {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (φ : A →ₗ[O] M) (c : M)
    (hφ : ∀ k, φ (aeval a (nP k)) = c) : φ L = c := by sorry
