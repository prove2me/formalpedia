-- Prove2me | Theorems.Thm_BunkbedFalse_wz_diff_poly
-- name    : BunkbedFalse.wz_diff_poly
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T00:08:30.9532+00:00
-- url     : https://prove2.me/theorems/35fba1dc-e3fa-483b-86e0-e2eb232d9281
-- title:
--   The Wierman--Ziff difference polynomial for Hollom's hypergraph
-- statement:
--   Consider the Wierman--Ziff five-state percolation model on Hollom's $3$-uniform hypergraph $H$, with transversal set $T = \{u_2, u_7, u_9\}$. Each of the six hyperedges of $H$ independently takes one of five states on each of the two levels of the bunkbed, the state recording which of its three vertices the hyperedge connects; a state $s$ occurs with probability $P_s$. Since there are six hyperedges and two levels, each connection probability is a sum over $5^{12}$ configurations, and is therefore a polynomial of degree $12$ in the five state probabilities.
--
--   This theorem evaluates that polynomial. Assume the model is symmetric in the two ways of joining the transversal vertex to one other vertex, $P_{ab|c} = P_{ac|b}$, and write
--   $$x = P_{abc}, \qquad y = P_{a|b|c}, \qquad z = P_{a|bc}, \qquad u = P_{ab|c} = P_{ac|b}.$$
--   Then the difference between the cross-level and the same-level connection probability of the two endpoints $u_1$ and $u_{10}$ is given exactly by
--
--   $$\mathbb{P}^{\mathrm{wz}}\bigl[u_1 \leftrightarrow u_{10}'\bigr] - \mathbb{P}^{\mathrm{wz}}\bigl[u_1 \leftrightarrow u_{10}\bigr] \;=\; \texttt{wzDiffPoly}(x,y,z,u),$$
--
--   where $\texttt{wzDiffPoly}$ is the explicit polynomial of the $\texttt{BunkbedWZPoly}$ definition: homogeneous of degree $12$, with $231$ monomials when expanded, presented in the graded form
--   $$\sum_{j=0}^{6} z^{j}\,W^{6-j}\,R_j \;+\; \sum_{j=7}^{12} z^{j}\,R_j, \qquad W = xy - u^2, \quad R_0 = 1.$$
--
--   Note that no hypothesis beyond the symmetry $P_{ab|c} = P_{ac|b}$ is needed: this is an identity between polynomials, valid for every $P$, and in particular it does not require $P$ to be a probability distribution.
--
--   **Mathematical role.** This is the combinatorial half of the robustness lemma (Lemma 3.3) of Gladkov--Pak--Zimin, isolated from the arithmetic half. Once the difference is known as an explicit polynomial, the strict inequality of Lemma 3.3 becomes a question of real algebra on a region of the simplex, which is the companion statement `BunkbedFalse.wzDiffPoly_pos`. The leading term $W^6$ is exactly the contribution of the configurations in which every hyperedge lies wholly on one level -- that is, of the alternative model -- and its coefficient $1$ is Hollom's $13 - 12$ from Lemma 3.1.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Lemma 3.3 (p. 3) and Sections 3.3-3.6 (pp. 3-6).

import Definitions.Def_BunkbedWZPoly
open Bunkbed Bunkbed.Hyper

namespace BunkbedFalse

/-- **The Wierman-Ziff difference polynomial** (Section 3 of Gladkov-Pak-Zimin). In the
symmetric case `P_ab|c = P_ac|b`, the difference between the cross-level and the same-level
connection probability on Hollom's hypergraph is the explicit degree-12 polynomial
`wzDiffPoly`. This is the combinatorial content of Lemma 3.3, separated from the arithmetic. -/
theorem wz_diff_poly (P : WZ → ℚ) (hsym : P .ab_c = P .ac_b) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2))
      - wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      = wzDiffPoly (P .abc) (P .a_b_c) (P .a_bc) (P .ab_c) := by
  sorry

end BunkbedFalse
