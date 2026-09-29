-- Prove2me | Theorems.Thm_Erdos9796FiniteNine_cyclic_forms
-- name    : Erdos9796FiniteNine.cyclic_forms
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T07:12:10.881519+00:00
-- url     : https://prove2.me/theorems/0ecda05b-fa42-4a3f-9e58-f77d7226bc26
-- title:
--   Finite-nine remaining cyclic form exclusions
-- statement:
--   Cyclic relabelling excludes the five remaining versions of the three escaped witness-location patterns at the second and third distinguished triangle vertices.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/tree/6e3e2a849c67f518d75fd45a09a201a6c8f4cd8f/lean/Erdos9796Proof/P97

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N8Interface

/-! Statement-only transfer node for the remaining cyclic form exclusions.

SKETCH — NOT PROMOTABLE. The source project already proves this result; the proof
solution will be transferred separately after this public theorem node exists.
-/

open scoped EuclideanGeometry

theorem Erdos9796FiniteNine.cyclic_forms {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A) :
    S.N4dExcludesFormA_v2 ∧ S.N4dExcludesFormC_v2 ∧
    S.N4dExcludesFormA_v3 ∧ S.N4dExcludesFormB_v3 ∧
    S.N4dExcludesFormC_v3 := by sorry
