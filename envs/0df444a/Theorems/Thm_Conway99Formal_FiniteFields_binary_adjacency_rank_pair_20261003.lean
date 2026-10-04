-- Prove2me | Theorems.Thm_Conway99Formal_FiniteFields_binary_adjacency_rank_pair_20261003
-- name    : Conway99Formal.FiniteFields.binary_adjacency_rank_pair_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:13:28.311055+00:00
-- url     : https://prove2.me/theorems/882701a8-7b13-464b-bb6f-6bba7053d0c2
-- title:
--   Exact binary adjacency ranks for a Conway-parameter graph
-- statement:
--   Let $G$ be a simple graph on the 99 labeled vertices $\operatorname{Fin}(99)$ that is strongly regular with parameters $(99,14,1,2)$. Write $A$ for its literal vertex adjacency matrix over $\mathbb F_2$ and $I$ for the identity matrix on the same vertices. Then
--
--   $$
--   \operatorname{rank}_{\mathbb F_2}(A)=54,\qquad\operatorname{rank}_{\mathbb F_2}(I+A)=45.
--   $$
--
--   These are necessary ranks for any such graph. They neither construct one nor prove nonexistence, and they do not establish the separate dual-distance or triangle-incidence claims.
-- source:
--   Conway99/Conway99/Claims/C04finitefieldranks.lean (SHA-256 dd4045131b6d6eeddb8be571417bf9208ddaac2bc8d6a4019c50313d381c884b), exact C04 rank-45 declaration; FiniteFieldCharpolyRank.lean at commit 556b9ec6164112b4b86f75858123d00a271dcbed; independently checked spectral source from formalization/2026-10-03/spectral-ranks/SpectralRanks.lean at 72d61144789e1e0ef8d6a3c8b4650b5ae5204273, source SHA-256 a425d0baabe9673d77205ed2a18cce974a548ade1e237dcdafa0d856f5fa7082. The proof uses the same graph throughout and only the displayed SRG hypothesis.

import Mathlib
set_option autoImplicit false
open Matrix

theorem Conway99Formal.FiniteFields.binary_adjacency_rank_pair_20261003 (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) : (G.adjMatrix (ZMod 2)).rank = 54 ∧ ((1 : Matrix (Fin 99) (Fin 99) (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 45 := by sorry
