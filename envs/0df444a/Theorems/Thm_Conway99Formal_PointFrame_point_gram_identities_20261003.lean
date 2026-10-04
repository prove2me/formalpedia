-- Prove2me | Theorems.Thm_Conway99Formal_PointFrame_point_gram_identities_20261003
-- name    : Conway99Formal.PointFrame.point_gram_identities_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-03T23:49:06.016049+00:00
-- url     : https://prove2.me/theorems/85fc91dd-eb44-4e34-a72a-382467a9b533
-- title:
--   Necessary point Gram identities for an SRG(99,14,1,2)
-- statement:
--   For any actual finite simple strongly regular graph G with parameters (99,14,1,2), form its real adjacency matrix A, point Gram Q=27I-9A+J, and normalized projector P=Q/63. Then Q²=63Q, Q is symmetric, QJ=0, P²=P, tr(Q)=2772, and tr(P)=44. These six identities are necessary for any hypothetical graph. They do not construct a graph, prove nonexistence, establish the rank-44 real frame, or establish any triangle or lattice claim.
-- source:
--   Conway99/Conway99/Core.lean Point.Delta_sq, Point.J_mul_Delta, Point.trace_Delta, Point.Eminus_idem, Point.trace_Eminus, SHA-256 1d5ecefb2efc22445bc7f494578876c5b25222ba4dda52ab10a5df38ec4feedb; clean-start proof-library.zip proofs/FOUNDATIONS.md §1, member SHA-256 32127d3ecb9cb533d4a019a1786ee17c84aedff5c8a121a42fc62253301d341c. The actual 44-row frame and lattice remain open in this package; see claims.json.

import Definitions.Def_Conway99_Point_Gram_20261003
set_option autoImplicit false
open Matrix SimpleGraph

theorem Conway99Formal.PointFrame.point_gram_identities_20261003 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) : (Conway99Formal.PointFrame.Q G * Conway99Formal.PointFrame.Q G = 63 • Conway99Formal.PointFrame.Q G) ∧ (Matrix.transpose (Conway99Formal.PointFrame.Q G) = Conway99Formal.PointFrame.Q G) ∧ (Conway99Formal.PointFrame.Q G * (Matrix.of 1 : Matrix V V ℝ) = 0) ∧ (Conway99Formal.PointFrame.P G * Conway99Formal.PointFrame.P G = Conway99Formal.PointFrame.P G) ∧ ((Conway99Formal.PointFrame.Q G).trace = 2772) ∧ ((Conway99Formal.PointFrame.P G).trace = 44) := by sorry
