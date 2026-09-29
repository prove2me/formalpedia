-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_zeta_almost_periodic
-- name    : DeBruijnNewman.Dobner.zeta_almost_periodic
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T21:41:33.832752+00:00
-- url     : https://prove2.me/theorems/30025596-f380-4bd2-8a2b-4780ce0b9e4e
-- title:
--   Bohr almost periods for Dobner's damped zeta series
-- statement:
--   Fix $t<0$ and let $Z_t$ be the Gaussian-damped zeta Dirichlet series. For every pair $a<b$ of real numbers, every $\varepsilon>0$, and every real lower bound $T$, there exists a real shift $\tau\geq T$ such that
--
--   $$
--   |Z_t(s+i\tau)-Z_t(s)|<\varepsilon
--   \qquad\text{for every }s\in\mathbb C
--   \text{ with }a\leq\operatorname{Re}s\leq b.
--   $$
--
--   This is the unbounded-shift consequence of Bohr's almost-periodicity theorem for the everywhere absolutely convergent series $Z_t$. The estimate is uniform over the entire infinite strip, allowing a fixed zero disk to be translated to arbitrarily large heights.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Theorem 5 (Bohr's theorem), p. 14, and its application to F_t in Section 3.1, pp. 14–15. This states only the consequence that the almost periods are unbounded above, not the stronger density bounds in Theorem 5.

import Definitions.Def_DeBruijnNewman_Dobner
open Metric

theorem DeBruijnNewman.Dobner.zeta_almost_periodic (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    ∃ τ : ℝ, T ≤ τ ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖DeBruijnNewman.Dobner.zetaT t (s + (τ : ℂ) * Complex.I)
          - DeBruijnNewman.Dobner.zetaT t s‖ < ε := by sorry
