-- Prove2me | Theorems.Thm_Erdos180_subdivisionLine_base_of_line_center
-- name    : Erdos180.subdivisionLine_base_of_line_center
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:07:50.098795+00:00
-- url     : https://prove2.me/theorems/8e299b0f-5f62-47a8-bae1-bc024581183e
-- title:
--   A copy of $S_k$ with a centre at a line has its bases at lines
-- statement:
--   Conversely, if a copy of $S_k$ in $I_q$ sends some centre to a line, it sends every base
--   to a line. With the preceding lemma this pins the copy entirely to one bipartition class.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2525-L2550

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionLine_base_of_line_center
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {C : SymplecticLine K}
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ L : SymplecticLine K,
      copy (.inl (.inl base)) = .inr L := by sorry
