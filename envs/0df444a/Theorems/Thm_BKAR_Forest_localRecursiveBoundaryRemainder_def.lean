-- Prove2me | Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_def
-- name    : BKAR.Forest.localRecursiveBoundaryRemainder_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:04.440852+00:00
-- url     : https://prove2.me/theorems/1b54797e-bd1e-4aad-a8b7-90c0d8812052
-- title:
--   Forest: local Recursive Boundary Remainder def
-- statement:
--   The Forest construction uses the local Recursive Boundary Remainder def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L39-L53
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L39-L53

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localRecursiveBoundaryRemainder_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ)) := by sorry
