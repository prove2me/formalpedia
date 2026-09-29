-- Prove2me | Theorems.Thm_Erdos9796FiniteNine_shell
-- name    : Erdos9796FiniteNine.shell
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T07:09:33.66661+00:00
-- url     : https://prove2.me/theorems/a8773adc-86d1-4bff-b1e3-5380e4ae8974
-- title:
--   Finite-nine endpoint shell
-- statement:
--   Every nine-point convex counterexample with four equidistant witnesses at each vertex determines a boundary triangle and three associated cap regions used in the subsequent case analysis.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/tree/6e3e2a849c67f518d75fd45a09a201a6c8f4cd8f/lean/Erdos9796Proof/P97/N9Endpoint

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N8Interface

/-! Statement-only transfer node for the finite-nine endpoint shell.

SKETCH — NOT PROMOTABLE. The source project already proves this result; the proof
solution will be transferred separately after this public theorem node exists.
-/

open scoped EuclideanGeometry

theorem Erdos9796FiniteNine.shell :
    ∀ {A : Finset ℝ²}, A.Nonempty → A.card = 9 →
      Batch3N9.Problem97.ConvexIndep A →
      Batch3N9.Problem97.HasNEquidistantProperty 4 A →
      Nonempty (Batch3N9.Problem97.FiniteEndpointShell A) := by sorry
