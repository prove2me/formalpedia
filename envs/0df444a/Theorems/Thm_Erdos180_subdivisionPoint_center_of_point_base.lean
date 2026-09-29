-- Prove2me | Theorems.Thm_Erdos180_subdivisionPoint_center_of_point_base
-- name    : Erdos180.subdivisionPoint_center_of_point_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:06:36.515918+00:00
-- url     : https://prove2.me/theorems/d7753055-a589-41e2-b919-ea933317f5a3
-- title:
--   A copy of $S_k$ based at points has its centres at points
-- statement:
--   If a copy of $S_k$ in $I_q$ sends some base to a point, then it sends every centre to a
--   point as well.
--
--   Bases and centres lie in the same bipartition class of $S_k$ (both are original vertices of
--   $K_{3,k}$, at even distance), so they land in the same class of $I_q$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1897-L1922

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionPoint_center_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ c : SymplecticPoint K,
      copy (.inl (.inr center)) = .inl c := by sorry
