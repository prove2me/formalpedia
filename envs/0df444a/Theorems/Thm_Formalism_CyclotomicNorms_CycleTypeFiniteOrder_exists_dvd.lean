-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_dvd
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:03.769019+00:00
-- url     : https://prove2.me/theorems/dba49e12-365f-4e40-868a-5c3b5fef4f81
-- title:
--   Cycle Type Finite Order: exists dvd
-- statement:
--   The Cycle Type Finite Order construction uses the exists dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L135-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L135-L173

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_dvd (hf : GoodPoly N f) (hrf : Finset.univ.val.map r = rootsBar f)
    (hσ : ∀ i, r (σ i) = r i ^ g) (S : Finset (Fin N)) (hS : ∀ i ∈ S, σ i ∈ S) :
    ∃ Q : (ZMod g)[X], Q.Monic ∧ Q ∣ f ∧ Q.natDegree = S.card ∧
      ∀ i ∈ S, (Q.map (algebraMap (ZMod g) (Fbar g))).eval (r i) = 0 := by sorry
