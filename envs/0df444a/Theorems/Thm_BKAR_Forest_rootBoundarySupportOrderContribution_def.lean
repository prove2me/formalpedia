-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_def
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:04:02.620867+00:00
-- url     : https://prove2.me/theorems/4bd336e4-b7fd-42d5-9ec9-0af1db7b5bed
-- title:
--   Forest: root Boundary Support Order Contribution def
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L544-L552
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L544-L552

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_def
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V)) :
    rootBoundarySupportOrderContribution choices ρ I order =
      (if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
        boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          I order ρ := by sorry
