-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_corollary_13_2_sign_of_p
-- name    : FlowsNetworks.TwoArcs.corollary_13_2_sign_of_p
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:53.691484+00:00
-- url     : https://prove2.me/theorems/e34f35dd-9ab3-4b84-bc09-76e19436fccd
-- title:
--   Chapter I, Corollary 13.2 — the sign of qᵢⱼ is the sign of pᵢⱼ
-- statement:
--   Let $[N;\mathcal A]$ be a network with sources $S$, disjoint sinks $T$ and finite nonnegative arc capacities, and let $A_i\neq A_j$ be two arcs. Let $\bar v_{ij}(\xi,\eta)$, $\xi,\eta\in[0,\infty]$, be the maximal flow value when the capacities of $A_i$ and $A_j$ are replaced by $\xi$ and $\eta$; let $q_{ij}$ be its difference quotient over admissible rectangles (real $\xi,\eta\ge0$, $\xi+h\ge0$, $\eta+k\ge0$, $hk\neq0$), and let
--
--   $$p_{ij} = \bar v_{ij}(\infty,\infty) - \bar v_{ij}(0,\infty) - \bar v_{ij}(\infty,0) + \bar v_{ij}(0,0)$$
--
--   in extended arithmetic (possibly $\pm\infty$ or indeterminate $\infty-\infty$). Then
--
--   1. if $p_{ij}>0$ (including $p_{ij}=\infty$), $q_{ij}>0$ on some admissible rectangle and $q_{ij}<0$ on none;
--   2. if $p_{ij}=0$ or $p_{ij}$ is indeterminate, $q_{ij}=0$ on every admissible rectangle;
--   3. if $p_{ij}<0$, $q_{ij}<0$ on some admissible rectangle and $q_{ij}>0$ on none.
--
--   The single number $p_{ij}$, computed from four maximal flow values, thus decides whether the two arcs reinforce, ignore or interfere with each other.
--
--   **Formalization Note** $p_{ij}$ is the four-way value `pValue` (indeterminate, $+\infty$, $-\infty$, real); case (c) also admits $p_{ij}=-\infty$, which the book's "$p_{ij}<0$" covers. The sentence before the corollary on p. 57 says $p_{ij}$ is "defined by (13.5)"; it is defined by (13.11), which is used. The difference quotient uses $\bar v_{ij}(\xi,\eta+k)$ in its third term (the book prints $\eta+h$).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 58, Corollary 13.2 (with (13.11), p. 55)

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Corollary 13.2, p. 58, with `p_ij` the constant (13.11):
(a) if `p_ij > 0` (including `p_ij = ∞`), then `q_ij` is sometimes `> 0` and never `< 0`;
(b) if `p_ij = 0` or `p_ij` is indeterminate (`∞ − ∞`), then `q_ij` is identically zero;
(c) if `p_ij < 0`, then `q_ij` is sometimes `< 0` and never `> 0`. -/
theorem corollary_13_2_sign_of_p {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) :
    ((pValue G c Ai Aj = ExtValue.posInf ∨
          ∃ r : ℝ, 0 < r ∧ pValue G c Ai Aj = ExtValue.real r) →
        (∃ ξ η h k : ℝ, IsAdmissible ξ η h k ∧ 0 < diffQuotient G c Ai Aj ξ η h k) ∧
          ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → ¬ diffQuotient G c Ai Aj ξ η h k < 0) ∧
      ((pValue G c Ai Aj = ExtValue.indeterminate ∨ pValue G c Ai Aj = ExtValue.real 0) →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k = 0) ∧
      ((pValue G c Ai Aj = ExtValue.negInf ∨
          ∃ r : ℝ, r < 0 ∧ pValue G c Ai Aj = ExtValue.real r) →
        (∃ ξ η h k : ℝ, IsAdmissible ξ η h k ∧ diffQuotient G c Ai Aj ξ η h k < 0) ∧
          ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → ¬ 0 < diffQuotient G c Ai Aj ξ η h k) := by sorry

end FlowsNetworks.TwoArcs
