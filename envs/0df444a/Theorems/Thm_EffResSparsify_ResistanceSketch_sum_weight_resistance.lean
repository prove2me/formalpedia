-- Prove2me | Theorems.Thm_EffResSparsify_ResistanceSketch_sum_weight_resistance
-- name    : EffResSparsify.ResistanceSketch.sum_weight_resistance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:11.86505+00:00
-- url     : https://prove2.me/theorems/5d5faa3b-c0a3-4b30-ba7b-6febc7a243a5
-- title:
--   §3, p. 8 — weighted effective resistances sum to n − 1: $\sum_e w_eR_e = n-1$
-- statement:
--   Let $G=(V,E,w)$ be a connected weighted graph on $n$ vertices with positive edge weights $w_e$, Laplacian $L=B^{\mathsf T}WB$, and pseudoinverse $L^+$. For an edge $e$ with tail $a$ and head $b$, let $R_e=(\chi_a-\chi_b)^{\mathsf T}L^+(\chi_a-\chi_b)$ be its effective resistance. Then
--   $$
--   \sum_{e\in E} w_e R_e = n-1 .
--   $$
--
--   In the paper the sum equals the trace of the projection $\Pi=W^{1/2}BL^+B^{\mathsf T}W^{1/2}$, whose diagonal entries are $w_eR_e$. The identity is used twice: it normalizes the sampling probabilities $p_e=w_eR_e/(n-1)$ of the sparsification algorithm, and in the proof of Lemma 9 it bounds $\sum_e w_e\|Z(\chi_a-\chi_b)\|^2$.
--
--   **Formalization Note** Parallel edges are allowed; simplicity is not needed. Connectivity forces $n\ge1$, so $n-1$ is computed in $\mathbb R$ without truncation.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 8, §3 (proof of Theorem 1: "Since ∑_e w_eR_e = Tr(Π) = n − 1 by Lemma 3.(iii)"); used again on p. 12 in the proof of Lemma 9

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph

namespace EffResSparsify.ResistanceSketch

open Matrix

/-- §3, p. 8 (used on p. 12 "by Lemma 3.(iii)"): for a connected weighted graph on `n` vertices,
`∑_e w_e R_e = Tr(Π) = n − 1`, where `R_e = (χ_tail − χ_head)ᵀ L⁺ (χ_tail − χ_head)` is the
effective resistance across the edge `e`. -/
theorem sum_weight_resistance {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : WGraph V E) (hconn : G.IsConnected) :
    ∑ e, G.w e * G.R (G.tail e) (G.head e) = (Fintype.card V : ℝ) - 1 := by sorry

end EffResSparsify.ResistanceSketch
