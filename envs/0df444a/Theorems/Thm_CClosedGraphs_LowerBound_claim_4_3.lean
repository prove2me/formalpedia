-- Prove2me | Theorems.Thm_CClosedGraphs_LowerBound_claim_4_3
-- name    : CClosedGraphs.LowerBound.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:15.190946+00:00
-- url     : https://prove2.me/theorems/c7927ed7-316a-40a8-80f6-6d79a45bcf6b
-- title:
--   Claim 4.3 (corrected count), pp. 12–13 — the constructed blow-up has Ω(c^{−3/2} 2^{c/2} n^{3/2}) maximal cliques
-- statement:
--   There is an absolute constant $C>0$ such that, for every $k\ge1$ and $h\ge2$, one can choose a graph $H$ on $2k$ vertices of girth at least $5$ whose blow-up $H^{(h)}$ has at least
--   $$
--   \#\mathrm{MC}\bigl(H^{(h)}\bigr) \ \ge\ C\,(2h)^{-3/2}\,2^h\,(2kh)^{3/2}
--   $$
--   maximal cliques. Here $c=2h$ and $n=2kh$, a positive multiple of $c$, so this is the paper's $\Omega(c^{-3/2}2^{c/2}n^{3/2})$ count for the constructed graph.
--
--   **Formalization Note** The printed proof counts $2^h$ distinct maximal cliques per edge. Two choices are $U_x$ and $U_y$, shared across edges, so only $2^h-2$ mixed cliques per edge are distinct. This correction preserves the $\Omega$ bound for $h\ge2$. The graph $H$ is chosen after $k,h$, as in the construction, while $C$ is absolute. The parameterization $c=2h$, $n=2kh$ retains the paper's in-construction assumptions that $c$ is even and $n$ is a positive multiple of $c$. The case $h=1$ is excluded because the blow-up is edgeless.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, pp. 12–13, Claim 4.3 and its proof (count corrected)

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

namespace CClosedGraphs.LowerBound
theorem claim_4_3 : ∃ C : ℝ, 0 < C ∧ ∀ k h : ℕ, 1 ≤ k → 2 ≤ h →
    ∃ H : SimpleGraph (Fin (2 * k)), 5 ≤ H.egirth ∧
      C * ((2 * h : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) * (2 : ℝ) ^ (h : ℝ) *
        ((2 * k * h : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
          (CClosedGraphs.Peeling.numMaxCliques (blowUp H h) : ℝ) := by sorry
end CClosedGraphs.LowerBound
