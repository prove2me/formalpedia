-- Prove2me | Theorems.Thm_Erdos9796FiniteNine_n4e_core
-- name    : Erdos9796FiniteNine.n4e_core
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-10T01:51:45.620378+00:00
-- url     : https://prove2.me/theorems/8092e252-3da6-454a-813c-702397a844f8
-- title:
--   Finite-nine N4e core support
-- statement:
--   Every nine-point endpoint configuration supplies the two-point cap-layout and geometric facts needed to exclude the remaining escaped witness-location patterns.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0707e2c26e2e570e2b56ce656242cf5dec4d2584/lean/Erdos9796Proof/P97/N9Endpoint/N4e.lean

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N4dPackets

open scoped EuclideanGeometry

/-- The first N4e slice supplies the explicit interface used by later branch proofs. -/

theorem Erdos9796FiniteNine.n4e_core {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A) :
    Nonempty (Batch3N9.Problem97.FiniteEndpointShell.N4eCoreSupport S) := by
  sorry
