-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_primeToPart_pow
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:40.473166+00:00
-- url     : https://prove2.me/theorems/21927dfe-16f9-4edd-a07b-e63e9a4d7b26
-- title:
--   Cycle Type Finite Order: prime To Part pow
-- statement:
--   The Cycle Type Finite Order construction uses the prime To Part pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L15-L18

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
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
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {M : Type*} [Monoid M]

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_pow (ℓ : ℕ) (x : M) (k : ℕ) (h : orderOf (x ^ k) = orderOf x) :
    primeToPart ℓ (x ^ k) = primeToPart ℓ x ^ k := by sorry
