-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_newton
-- name    : Formalism.NG.IdemLiftAlt.newton
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:02.35832+00:00
-- url     : https://prove2.me/theorems/283f0ecb-a1b4-4853-8d6d-8bb2a7bff4bd
-- title:
--   Idem Lift Alt: newton
-- statement:
--   The Idem Lift Alt construction uses the newton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L135-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L135-L201

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

theorem Formalism.NG.IdemLiftAlt.newton (a : A) (n : ℕ)
    (hn : (a ^ 2 - a) ^ n ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A)) :
    ∃ L : A, IsIdempotentElem L ∧ ∀ j : ℕ,
      aeval a (nP (n + j)) - L ∈ IsLocalRing.maximalIdeal O ^ j • (⊤ : Submodule O A) := by sorry
