-- Prove2me | Theorems.Thm_Erdos180_subdivisionLine_pair_incidence
-- name    : Erdos180.subdivisionLine_pair_incidence
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:07:13.468084+00:00
-- url     : https://prove2.me/theorems/2af9b14d-5aa2-4d3f-8a21-bb9718e04b31
-- title:
--   A copy of $S_k$ based at lines: the joining point
-- statement:
--   Dually: if a copy of $S_k$ in $I_q$ sends a base to a line $L$ and a centre to a line $C$,
--   then the subdivision vertex between them lands on a point $p$ incident to both.
--
--   The source uses both bipartition classes: excluding $\mathcal{J}$ constrains one class, and for
--   even $q$ the self-duality of $W(q)$ transfers the conclusion to the other (Proposition 4.2).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2470-L2496

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionLine_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L C : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L)
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ p : SymplecticPoint K,
      copy (.inr (base, center)) = .inl p ∧
        p.1 ≤ L.1 ∧ p.1 ≤ C.1 := by sorry
