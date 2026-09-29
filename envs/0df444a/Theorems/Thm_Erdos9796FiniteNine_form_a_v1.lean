-- Prove2me | Theorems.Thm_Erdos9796FiniteNine_form_a_v1
-- name    : Erdos9796FiniteNine.form_a_v1
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T07:11:00.005691+00:00
-- url     : https://prove2.me/theorems/34a0a695-2a9d-47f4-b9c6-c3b38c82705d
-- title:
--   Finite-nine escaped Form a exclusion at v1
-- statement:
--   At the first distinguished triangle vertex, an escaping four-point distance class cannot contain one point in each of the other two cap interiors.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/tree/6e3e2a849c67f518d75fd45a09a201a6c8f4cd8f/lean/Erdos9796Proof/P97

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N8Interface

/-! Statement-only transfer node for the escaped Form a exclusion at `v₁`.

SKETCH — NOT PROMOTABLE. The source project already proves this result; the proof
solution will be transferred separately after this public theorem node exists.
-/

open scoped EuclideanGeometry

theorem Erdos9796FiniteNine.form_a_v1 {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (hB2 : S.N4dExcludesFormB_v2) :
    S.N4dExcludesFormA_v1 := by sorry
