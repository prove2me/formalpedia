-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesBoundaryExpansion_continuous_comp
-- name    : BKAR.BKARContDiff.allBranchesBoundaryExpansion_continuous_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:39.215999+00:00
-- url     : https://prove2.me/theorems/a83d94b4-7c3c-44a9-9baf-9851a867487e
-- title:
--   BKARCont Diff: all Branches Boundary Expansion continuous comp
-- statement:
--   The boundary-only all-branches expansion is continuous along any fixed-length
--   coordinatewise-continuous parameter-list path.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L166-L246
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L166-L246

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesBoundaryExpansion_continuous_comp
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      {X : Type*} [TopologicalSpace X]
      {tsPath : X → List ℝ} {topPath : X → ℝ},
      BKAR.ListPathContinuous pref.length tsPath →
      Continuous topPath →
      Continuous
        (fun x : X =>
          Forest.allBranchesBoundaryExpansion choices n F pref
            (tsPath x) (topPath x) ρ)
  := by sorry
