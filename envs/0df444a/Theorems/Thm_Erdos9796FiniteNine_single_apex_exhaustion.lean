-- Prove2me | Theorems.Thm_Erdos9796FiniteNine_single_apex_exhaustion
-- name    : Erdos9796FiniteNine.single_apex_exhaustion
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T07:13:35.984986+00:00
-- url     : https://prove2.me/theorems/b5c8965d-f45d-4911-a606-655ddfa6899d
-- title:
--   Finite-nine single-apex exhaustion
-- statement:
--   Under cap containment and the four-equidistant-witness property, no point of the nine-point configuration lies in the interior of any endpoint cap.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/tree/6e3e2a849c67f518d75fd45a09a201a6c8f4cd8f/lean/Erdos9796Proof/P97/N8

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N8Interface

/-! Statement-only transfer node for the finite-nine single-apex exhaustion.

SKETCH — NOT PROMOTABLE. The source project already proves this result; the proof
solution will be transferred separately after this public theorem node exists.
-/

open scoped EuclideanGeometry

theorem Erdos9796FiniteNine.single_apex_exhaustion {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment)
    (hK4 : Batch3N9.Problem97.HasNEquidistantProperty 4 A)
    {x : ℝ²} {i : Fin 3} (hxcap : x ∈ S.capInteriorByIndex i) :
    False := by sorry
