-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_lemma_A_2
-- name    : DecBilevel.SLDBO.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:34.40322+00:00
-- url     : https://prove2.me/theorems/2a11d228-8128-4bd7-9e8b-766ebe1f53a6
-- title:
--   Lemma A.2, p. 14 — projection onto a ball does not increase the consensus error
-- statement:
--   Let $r\ge0$ and let $\mathcal P_r$ be the Euclidean projection onto the closed ball of radius $r$ in $\mathbb R^d$. For any $x_1,\dots,x_n\in\mathbb R^d$,
--   $$\sum_{i=1}^n\Big\|\mathcal P_r[x_i]-\frac1n\sum_{j=1}^n\mathcal P_r[x_j]\Big\|^2\le\sum_{i=1}^n\Big\|x_i-\frac1n\sum_{j=1}^nx_j\Big\|^2.$$
--
--   This is what allows SLDBO to project $v^k$ without losing the consensus contraction of gradient tracking.
--
--   **Formalization Note.** $\mathcal P_r$ is the closed form `ballProj r`: $z$ if $\|z\|\le r$, else $\frac r{\|z\|}z$.
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 14, Lemma A.2

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem lemma_A_2 {n d : ℕ} (r : ℝ) (hr : 0 ≤ r) (z : Fin n → E d) :
    ∑ i, ‖ballProj r (z i) - avg (fun j => ballProj r (z j))‖ ^ 2 ≤
      ∑ i, ‖z i - avg z‖ ^ 2 := by sorry

end DecBilevel.SLDBO
