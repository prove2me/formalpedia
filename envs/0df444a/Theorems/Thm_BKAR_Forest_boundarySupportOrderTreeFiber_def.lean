-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_def
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:03.423426+00:00
-- url     : https://prove2.me/theorems/3ee8d1d5-a59b-577b-a83e-0029f6270e5c
-- title:
--   Forest: boundary Support Order Tree Fiber def
-- statement:
--   The Forest construction uses the boundary Support Order Tree Fiber def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L47-L60
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L47-L60

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I order ρ =
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t I order ρ) := by sorry
