-- Prove2me | Theorems.Thm_BollobasChromatic_Main_display_5
-- name    : BollobasChromatic.Main.display_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:16.800916+00:00
-- url     : https://prove2.me/theorems/28400bfc-bf3e-4b2c-a5e4-c41391aaf093
-- title:
--   (5), p. 51 — P(X ≤ E(X) − a) ≤ exp{−a²/(2(a+N))} for the edge-disjoint K^r packing number X of G(n,p)
-- statement:
--   Let $0<p<1$, $n,r\ge 0$, $N=\binom n2$, and let $X=X(G_p)$ be the maximal number of pairwise edge-disjoint $K^r$ subgraphs of the random graph $G_p=G_{n,p}$. For every $a>0$,
--   $$
--   \mathbb P\bigl(X\le \mathbb E(X)-a\bigr)\le \exp\Bigl\{-\frac{a^2}{2(a+N)}\Bigr\}.
--   $$
--
--   This is the concentration step of the proof of Theorem 2: together with the lower bound (9) on $\mathbb E(X)$ it shows that $G_p$ has fewer than $(1-c)E(n,r)$ $r$-cliques only with exponentially small probability.
--
--   **Formalization Note** The paper is in the setting $r\ge 3$ of Theorem 2; the bound holds for every $r$, so no restriction on $r$ is stated (a stronger statement).
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 51, proof of Theorem 2, display (5)

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem display_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n r : ℕ) (a : ℝ) (ha : 0 < a) :
    gnpProb n p (fun G => (packingNum G r : ℝ) ≤ gnpExp n p (fun G => (packingNum G r : ℝ)) - a) ≤
      Real.exp (-(a ^ 2 / (2 * (a + (n.choose 2 : ℝ))))) := by sorry

end BollobasChromatic.Main
