-- Prove2me | Theorems.Thm_Erdos180_subdivisionPoint_base_center_related
-- name    : Erdos180.subdivisionPoint_base_center_related
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:06:54.454281+00:00
-- url     : https://prove2.me/theorems/b60c59a0-e710-4972-a827-efc3abfd0d0b
-- title:
--   Bases and centres of a copy of $S_k$ are related
-- statement:
--   If a copy of $S_k$ in $I_q$ sends a base to $p$ and a centre to $c$, then $p \sim c$ in
--   the common-neighbour graph of the point class.
--
--   They are joined by a two-edge path through the image of the subdivision vertex, which is exactly
--   what $\sim$ records. This is the direction of Lemma 3.1(2) stating that the centres of a copy
--   of $S_k$ with base set $T$ belong to $L(T)$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1953-L1973

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionPoint_base_center_related
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    SymplecticPointRelated K p c := by sorry
