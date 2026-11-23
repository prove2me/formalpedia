-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_iter_eq
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.iter_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:26.044485+00:00
-- url     : https://prove2.me/theorems/07565cd1-833d-4059-a796-9f5e317df601
-- title:
--   Cycle Type Finite Order: iter eq
-- statement:
--   The Cycle Type Finite Order construction uses the iter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L115-L119

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
variable {g : ℕ} [hg : Fact g.Prime]
variable {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.iter_eq (hσ : ∀ i, r (σ i) = r i ^ g) (n : ℕ) (i : Fin N) :
    r ((σ ^ n) i) = r i ^ (g ^ n) := by sorry
