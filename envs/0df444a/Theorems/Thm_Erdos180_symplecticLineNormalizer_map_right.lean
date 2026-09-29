-- Prove2me | Theorems.Thm_Erdos180_symplecticLineNormalizer_map_right
-- name    : Erdos180.symplecticLineNormalizer_map_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:16:43.880125+00:00
-- url     : https://prove2.me/theorems/4d928744-ce44-4363-a697-1b39f5e8f113
-- title:
--   Normalising the second line of a disjoint pair
-- statement:
--   The same automorphism carries $M$ to the standard vertical line. With the previous lemma:
--   any two disjoint lines of $W(q)$ may be moved simultaneously to the horizontal and vertical
--   coordinate lines.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7240-L7274

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticLineNormalizer_map_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) M =
      symplecticVerticalLine K := by sorry
