-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_primeToPart_coprime
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:45.021102+00:00
-- url     : https://prove2.me/theorems/c03ebdf3-42c9-4bd0-a071-8d4eff68a2b5
-- title:
--   Cycle Type Finite Order: prime To Part coprime
-- statement:
--   The Cycle Type Finite Order construction uses the prime To Part coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L20-L32

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_coprime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    (orderOf (primeToPart ℓ x)).Coprime ℓ := by sorry
