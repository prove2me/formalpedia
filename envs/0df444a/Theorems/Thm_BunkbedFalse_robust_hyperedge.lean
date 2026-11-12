-- Prove2me | Theorems.Thm_BunkbedFalse_robust_hyperedge
-- name    : BunkbedFalse.robust_hyperedge
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:58:42.94899+00:00
-- url     : https://prove2.me/theorems/be71f99b-f956-4657-99f9-32d4fb851fb6
-- title:
--   Lemma 3.3 — the robust hyperedge lemma
-- statement:
--   Let $H$ be Hollom's hypergraph with transversal set $T = \{u_2,u_7,u_9\}$, and consider Wierman–Ziff percolation on the associated bunkbed hypergraph, in which each hyperedge independently takes one of five states with probabilities $P_{abc}$, $P_{a|b|c}$, $P_{a|bc}$, $P_{ab|c}$, $P_{ac|b}$ summing to $1$. Assume the model's symmetry $P_{ab|c} = P_{ac|b}$, the **nondegeneracy** condition $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b} > 0$, and the **robustness hypothesis**
--
--   $$400\,P_{a|bc} \;\le\; P_{abc}\,P_{a|b|c} \;-\; P_{ab|c}\,P_{ac|b}.$$
--
--   Then
--
--   $$\mathbb{P}^{\mathrm{wz}}\bigl(u_1 \leftrightarrow u_{10}\bigr) \;<\; \mathbb{P}^{\mathrm{wz}}\bigl(u_1 \leftrightarrow u'_{10}\bigr).$$
--
--   This is the **robust hyperedge lemma** and the technical heart of the refutation. Hollom's computation applies only to the exact hypergraph model; this lemma shows the strict inequality survives in the far more flexible WZ model, and therefore survives the inexact simulation of a hyperedge by a gadget graph. The source proves it by constructing a weight-preserving involution on a refined configuration space, built from a reflection involution and a half-reflection involution.
--
--   **Formalization Note** The hypothesis that the five probabilities are nonnegative and sum to $1$ is stated explicitly. The source notes (§8.2) that this lemma is a finite problem — positivity of degree-$2$ polynomials in five variables with at most $5^{12}$ nonzero coefficients on a region of the unit cube — and that it was independently verified by computer; a formal proof would replace that check with a certificate.
--
--   **⚠️ Deviation from the printed statement.** The published Lemma 3.3 does not include the nondegeneracy hypothesis $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b} > 0$, and **is false without it**. Take
--   $$P_{abc} = u^2,\quad P_{ab|c} = P_{ac|b} = u(1-u),\quad P_{a|bc} = 0,\quad P_{a|b|c} = (1-u)^2 \qquad (0 \le u \le 1).$$
--   These are nonnegative, sum to $1$, satisfy the symmetry, and satisfy Eq. [1] as $0 \le 0$. But this is precisely the case in which each hyperedge degenerates into two *independent ordinary edges* $a$–$b$ and $a$–$c$. Every edge of the resulting graph is then incident to a transversal vertex; the posts identify $u_2, u_7, u_9$ across the two levels; and $u_1$ and $u_{10}$ each hang off a single transversal vertex by one edge. Both probabilities therefore factor as $u^2 \cdot \Pr[u_2 \sim u_9]$ and are **exactly equal**, so the strict conclusion fails. (At $u = 1/2$ both equal $734377/4194304$.)
--
--   The source's own proof needs this hypothesis: it divides by $Z = 2(P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}) + 2P_{a|bc} - P_{a|bc}^2$, which vanishes on exactly this family, and it concludes strictly only when the conditioning event has positive probability. The hypothesis is satisfied in the intended application, since Lemma 4.1 supplies a strictly positive value.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 3, Lemma 3.3 (Eqs. [1] and [2]); proof pp. 5-7.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Lemma 3.3** (robust hyperedge lemma, p. 3), with the nondegeneracy hypothesis `hpos`
added: the printed statement is false without it. -/
theorem robust_hyperedge (P : WZ → ℚ)
    (hnn : ∀ s, 0 ≤ P s)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1)
    (hsym : P .ab_c = P .ac_b)
    (hpos : 0 < P .abc * P .a_b_c - P .ab_c * P .ac_b)
    (h400 : 400 * P .a_bc ≤ P .abc * P .a_b_c - P .ab_c * P .ac_b) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      < wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) := by
  sorry

end BunkbedFalse
