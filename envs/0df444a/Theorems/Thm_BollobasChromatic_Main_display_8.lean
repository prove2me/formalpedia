-- Prove2me | Theorems.Thm_BollobasChromatic_Main_display_8
-- name    : BollobasChromatic.Main.display_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:32.740362+00:00
-- url     : https://prove2.me/theorems/4757578d-8dbb-4165-848e-da52666c0d7b
-- title:
--   (8), p. 51 — E(Z_l|A) = C(r,l)C(n−r,r−l)p^{C(r,2)−C(l,2)} = F_l, stated as E(Z_l·1_A) = P(A)·F_l
-- statement:
--   Let $n\ge r$ and $2\le l\le r-1$. In $G_p=G_{n,p}$ let $W=[r]$, let $A$ be the event that $W$ spans a complete graph, and let $Z_l$ be the number of $K^r$ subgraphs with exactly $l$ vertices in $W$. Then
--   $$
--   \mathbb E\bigl(Z_l\,\mathbf 1_A\bigr)=p^{\binom r2}\cdot\binom rl\binom{n-r}{r-l}p^{\binom r2-\binom l2},
--   $$
--   that is, since $\mathbb P(A)=p^{\binom r2}$, $\mathbb E(Z_l\mid A)=\binom rl\binom{n-r}{r-l}p^{\binom r2-\binom l2}=F_l$.
--
--   With (6) and (7) this gives $\mathbb E(X')\ge\binom nr\mathbb P(A)\bigl(1-\sum_{l=2}^{r-1}F_l\bigr)$.
--
--   **Formalization Note** The identity is stated without conditioning, multiplied by $\mathbb P(A)$. Both sides are polynomials in $p$ and the identity holds for every real $p$, so the standing $0<p<1$ is dropped (a stronger statement).
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 51, proof of Theorem 2, display (8)

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics
open scoped Classical

theorem display_8 (p : ℝ) (n r l : ℕ) (hrn : r ≤ n) (hl2 : 2 ≤ l) (hlr : l ≤ r - 1) :
    gnpExp n p (fun G => if G.IsClique (baseSet n r : Set (Fin n)) then
        (cliquesMeeting G r l : ℝ) else 0) =
      p ^ r.choose 2 *
        ((r.choose l : ℝ) * ((n - r).choose (r - l) : ℝ) * p ^ (r.choose 2 - l.choose 2)) := by sorry

end BollobasChromatic.Main
