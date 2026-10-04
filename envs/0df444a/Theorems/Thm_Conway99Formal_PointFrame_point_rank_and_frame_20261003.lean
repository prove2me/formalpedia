-- Prove2me | Theorems.Thm_Conway99Formal_PointFrame_point_rank_and_frame_20261003
-- name    : Conway99Formal.PointFrame.point_rank_and_frame_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:19:32.044789+00:00
-- url     : https://prove2.me/theorems/f437463d-aefd-470f-8dc6-c3d287975aa2
-- title:
--   Real point ranks and actual 44-row frame of a Conway graph
-- statement:
--   For every finite simple graph G with the strongly regular parameters (99,14,1,2), the normalized projector P(G)=Q(G)/63 and the real point Gram Q(G)=27I-9A+J both have rank 44. The same graph has a real point matrix Pi with 44 rows in its literal vertex coordinates, with Gram Q(G), row Gram 63I, zero column sum, and adjacency action Pi A=-4Pi. These are necessary consequences of a hypothetical graph; they neither construct such a graph nor prove nonexistence. The real coordinates are not asserted to be integers.
-- source:
--   Conway99/Conway99/Core.lean Point.Delta_sq, Point.Eminus_idem, Point.trace_Eminus, Point.rank_Eminus, SHA-256 1d5ecefb2efc22445bc7f494578876c5b25222ba4dda52ab10a5df38ec4feedb; archive/clean-start/proof-library.zip proofs/FOUNDATIONS.md §1, member SHA-256 32127d3ecb9cb533d4a019a1786ee17c84aedff5c8a121a42fc62253301d341c.

import Definitions.Def_Conway99_Point_Gram_20261003
set_option autoImplicit false
open Matrix SimpleGraph

theorem Conway99Formal.PointFrame.point_rank_and_frame_20261003 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) : (Conway99Formal.PointFrame.P G).rank = 44 ∧ (Conway99Formal.PointFrame.Q G).rank = 44 ∧ ∃ Pi : Matrix (Fin 44) V ℝ, Piᵀ * Pi = Conway99Formal.PointFrame.Q G ∧ Pi * Piᵀ = (63 : ℝ) • (1 : Matrix (Fin 44) (Fin 44) ℝ) ∧ Pi.mulVec (fun _ => 1) = 0 ∧ Pi * G.adjMatrix ℝ = -((4 : ℝ) • Pi) := by sorry
