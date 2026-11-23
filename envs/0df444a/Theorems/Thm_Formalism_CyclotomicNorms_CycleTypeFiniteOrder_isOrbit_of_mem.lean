-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_isOrbit_of_mem
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOrbit_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:51.74381+00:00
-- url     : https://prove2.me/theorems/2a4e9da8-35e5-433d-8668-0dcaf07798f9
-- title:
--   Cycle Type Finite Order: is Orbit of mem
-- statement:
--   The Cycle Type Finite Order construction uses the is Orbit of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L278-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L278-L291

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
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
variable {σ L}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOrbit_of_mem {q : ℕ} (hL : ∀ i, L (σ i) = L i ^ q) {S : Finset K} (hS : S ∈ blocks σ L) :
    Formalism.GaloisIrreducibility.IsOrbit (fun x : K => x ^ q) S := by sorry
