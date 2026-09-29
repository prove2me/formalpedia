-- Prove2me | Theorems.Thm_Erdos180_symplecticAutomorphism_disjoint_iff
-- name    : Erdos180.symplecticAutomorphism_disjoint_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:18:18.693169+00:00
-- url     : https://prove2.me/theorems/f7832408-2d4e-4cb1-bbac-b62f8098f303
-- title:
--   Automorphisms preserve disjointness of lines
-- statement:
--   For a symplectic automorphism $e$ and lines $L, M$,
--
--   $$e(L) \cap e(M) = 0 \iff L \cap M = 0 .$$
--
--   Disjointness of lines is the negation of the relation $\sim$ on the line class, so the
--   automorphism group acts on the common-neighbour graph $R_{\mathcal{M}}$ as well — which is what
--   allows the normalisation to be applied inside the pattern analysis.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7868-L7882

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticAutomorphism_disjoint_iff
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K) :
    Disjoint (symplecticAutomorphismLine K e L).1
        (symplecticAutomorphismLine K e M).1 ↔
      Disjoint L.1 M.1 := by sorry
