-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiberNontrivialIntegrable_of_le
-- name    : BKAR.Forest.boundarySupportOrderTreeFiberNontrivialIntegrable_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:22.04412+00:00
-- url     : https://prove2.me/theorems/11537bbd-80f6-5380-8562-12d5ea331773
-- title:
--   Forest: boundary Support Order Tree Fiber Nontrivial Integrable of le
-- statement:
--   The Forest construction uses the boundary Support Order Tree Fiber Nontrivial Integrable of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L283-L302
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L283-L302

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiberNontrivialIntegrable_of_le
    (choices : ActiveExtensionChoice V) :
    ∀ {m n : Nat} {F : Forest V} {pref : List (Edge V)}
      {prefixTs : List ℝ} {top : ℝ} {ρ : (Edge V → ℝ) → ℝ},
      m ≤ n →
      boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeFiberNontrivialIntegrable choices m
        F pref prefixTs top ρ
  := by sorry
