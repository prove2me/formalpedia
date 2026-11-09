-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_proposition_2_1
-- name    : DetStreamClique.MaxClique.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:12.486062+00:00
-- url     : https://prove2.me/theorems/7d9b0060-7203-4778-89a4-bff41270f37d
-- title:
--   Proposition 2.1 — clique size in a uniform random graph
-- statement:
--   For every integer $n\ge1$, sample a simple graph $G$ on $\operatorname{Fin}(n)$ by realizing each unordered edge independently with probability $1/2$. Then
--   $$\Pr\bigl(\omega(G)\le3\log_2 n\bigr)\ge1-1/n.$$
--   Probability is the published $G(n,p)$ finite graph law at $p=1/2$. This bounds the sizes of cliques in the random base graph and, with the same law, its complement.
--
--   Differences from the source:
--   - encoding: G∼G(n,1/2), with log base two and the term 1/n → n≥1, vertices Fin n, and the published finite-sum G(n,1/2) probability; reason: the source has no sufficiently-large qualifier; n=0 is excluded only because 1/n is undefined there
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Proposition 2.1, p. 6

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_HardInstance

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Proposition 2.1, p. 6: the uniform G(n,1/2) law, with no large-n restriction. -/
theorem proposition_2_1 (n : ℕ) (hn : 1 ≤ n) :
    1 - 1 / (n : ℝ) ≤ graphProbability n
      (fun G => (G.cliqueNum : ℝ) ≤ 3 * Real.logb 2 (n : ℝ)) := by sorry

end DetStreamClique.MaxClique
