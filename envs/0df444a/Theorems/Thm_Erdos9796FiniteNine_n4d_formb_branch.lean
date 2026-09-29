-- Prove2me | Theorems.Thm_Erdos9796FiniteNine_n4d_formb_branch
-- name    : Erdos9796FiniteNine.n4d_formb_branch
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-10T02:40:00.223866+00:00
-- url     : https://prove2.me/theorems/42459e69-2295-4399-8a78-05eecc61a975
-- title:
--   Finite-nine N4d Form B branch contradictions
-- statement:
--   For every nine-point endpoint configuration in which each cap interior contains exactly two points, eight geometric contradictions rule out the interior-point/opposite-vertex witness pattern.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0707e2c26e2e570e2b56ce656242cf5dec4d2584/lean/Erdos9796Proof/P97/N9Endpoint/N4e.lean

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N4dFormBBranchSupport

open scoped EuclideanGeometry

/-- The middle N4e slice supplies the branch conclusions used by the final Form B proof. -/

theorem Erdos9796FiniteNine.n4d_formb_branch {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (Z : Batch3N9.Problem97.FiniteEndpointShell.ZeroDefectCapLayout S) :
    Nonempty
      (Batch3N9.Problem97.FiniteEndpointShell.N4dFormBBranchSupport S Z) := by
  sorry
