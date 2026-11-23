-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_primeToPart_isOfFinOrder
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_isOfFinOrder
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:36.814647+00:00
-- url     : https://prove2.me/theorems/b530b25e-8ac6-4a4f-a5b6-4764cd0026ec
-- title:
--   Cycle Type Finite Order: prime To Part is Of Fin Order
-- statement:
--   The Cycle Type Finite Order construction uses the prime To Part is Of Fin Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L34-L35

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_isOfFinOrder (ℓ : ℕ) (x : M) (hx : IsOfFinOrder x) :
    IsOfFinOrder (primeToPart ℓ x) := by sorry
