-- Prove2me | Theorems.Thm_Erdos180_symplecticAutomorphismLineEquiv_apply
-- name    : Erdos180.symplecticAutomorphismLineEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:16:04.90628+00:00
-- url     : https://prove2.me/theorems/0b423343-5285-4b8c-8df8-1bd21fdb1b33
-- title:
--   The automorphism action on lines, as an equivalence
-- statement:
--   The equivalence of the line class induced by a symplectic automorphism agrees with the
--   direct action on lines. A coherence lemma making the bijective and the functional forms of the
--   action interchangeable.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6827-L6834

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

@[simp]
theorem Erdos180.symplecticAutomorphismLineEquiv_apply
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) :
    symplecticAutomorphismLineEquiv K e L =
      symplecticAutomorphismLine K e L := by sorry
