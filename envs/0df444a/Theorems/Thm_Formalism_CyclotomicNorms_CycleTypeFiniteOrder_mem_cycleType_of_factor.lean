-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_cycleType_of_factor
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_cycleType_of_factor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:51.009958+00:00
-- url     : https://prove2.me/theorems/6eaf0e20-2a5f-40bb-9378-67c8b867db04
-- title:
--   Cycle Type Finite Order: mem cycle Type of factor
-- statement:
--   The Cycle Type Finite Order construction uses the mem cycle Type of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L189-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L189-L255

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
variable {g : ℕ} [hg : Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_cycleType_of_factor (hf : GoodPoly N f) (hr : Function.Injective r)
    (hrf : Finset.univ.val.map r = rootsBar f) (hσ : ∀ i, r (σ i) = r i ^ g)
    (q : (ZMod g)[X]) (hq : Irreducible q) (hqf : q ∣ f) (hp : q.natDegree.Prime) :
    q.natDegree ∈ σ.cycleType := by sorry
