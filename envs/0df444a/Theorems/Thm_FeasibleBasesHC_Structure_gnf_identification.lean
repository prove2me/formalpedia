-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_gnf_identification
-- name    : FeasibleBasesHC.Structure.gnf_identification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:57.166846+00:00
-- url     : https://prove2.me/theorems/f0c9fa90-30e7-4912-aeeb-f1cc48ed68e5
-- title:
--   §3.2, p. 6 — identification with generalized network flow on G′
-- statement:
--   For a loopless digraph $G$, $0<\beta<1$, and a flow-slack pair $(x,y)$, assign $x_{ij}$ to the split arc $(w_i,v_j)$ and $y_i$ to $(v_i,w_i)$. Using the supplies implied by (2.10)–(2.13), this gives exactly the GNF formulation:
--
--   $$(x,y)\in\mathcal{WH}_\beta(G)\quad\Longleftrightarrow\quad f_{x,y}\in P_\beta(G').$$
--
--   The equivalence allows statements about bases of the original polytope to be studied through the split digraph.
--
--   **Formalization Note** Paper node $1$ is `0 : Fin n`; `[NeZero n]` ensures it exists. Nonexistent arcs carry zero flow, and uncapacitated original arcs have optional upper capacity `none`. The printed supply vector has $-\beta^{n-1}$ at $v_1$, but the defining equations require $-\beta^n$; the latter is used here.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, pp. 6–7, §3.2, unnumbered GNF identification and supply vector

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- The identification of (2.10)--(2.15) with GNF on the split digraph. -/
theorem gnf_identification {n : ℕ} [NeZero n] (G : Digraph n)
    (beta : ℝ) (hpos : 0 < beta) (hlt : beta < 1)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) :
    WH G beta x y ↔ (Gp G beta).IsFlow (splitFlow x y) := by sorry

end FeasibleBasesHC.Structure
