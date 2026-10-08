-- Prove2me | Theorems.Thm_BollobasChromatic_Main_display_6
-- name    : BollobasChromatic.Main.display_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:22.556196+00:00
-- url     : https://prove2.me/theorems/83703de5-cf0b-419b-be21-2408d291c834
-- title:
--   (6), p. 51 — E(X') ≥ C(n,r)·P(A){1 − E(Z|A)}, written as C(n,r)(P(A) − E(Z·1_A)) ≤ E(X')
-- statement:
--   Let $0<p<1$ and $0\le r\le n$. In $G_p=G_{n,p}$ let $X'$ be the number of $K^r$ subgraphs sharing no edge with another $K^r$ subgraph, let $W=[r]$, let $A$ be the event that $W$ spans a complete graph $K_0$ in $G_p$, and let $Z=\sum_{l=2}^{r-1}Z_l$, where $Z_l$ is the number of $K^r$ subgraphs of $G_p$ with exactly $l$ vertices in $W$. Then
--   $$
--   \binom nr\Bigl(\mathbb P(A)-\mathbb E\bigl(Z\,\mathbf 1_A\bigr)\Bigr)\le \mathbb E(X') .
--   $$
--   Since $\mathbb E(Z\mathbf 1_A)=\mathbb P(A)\,\mathbb E(Z\mid A)$, this is the paper's inequality $\mathbb E(X')\ge\binom nr\mathbb P(A)\{1-\mathbb E(Z\mid A)\}$.
--
--   It reduces the lower bound on $\mathbb E(X')$, hence on $\mathbb E(X)$, to the computation of $\mathbb E(Z_l\mid A)$ in (8).
--
--   **Formalization Note** The page prints the intermediate equality as $\mathbb E(X')=\binom nr\mathbb P(Z=0\mid A)$; the correct value is $\binom nr\mathbb P(A)\mathbb P(Z=0\mid A)$. The inequality, which is what the proof uses, is stated, without conditional probabilities. The condition $r\le n$ ($W=[r]\subseteq[n]$) is implicit on the page.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 51, proof of Theorem 2, display (6)

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics
open scoped Classical

theorem display_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n r : ℕ) (hrn : r ≤ n) :
    (n.choose r : ℝ) *
        (gnpProb n p (fun G => G.IsClique (baseSet n r : Set (Fin n))) -
          gnpExp n p (fun G => if G.IsClique (baseSet n r : Set (Fin n)) then
            ∑ l ∈ Finset.Icc 2 (r - 1), (cliquesMeeting G r l : ℝ) else 0)) ≤
      gnpExp n p (fun G => (isolatedCliqueCount G r : ℝ)) := by sorry

end BollobasChromatic.Main
