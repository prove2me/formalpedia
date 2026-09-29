-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_zeta_zero_disk
-- name    : DeBruijnNewman.Dobner.zeta_zero_disk
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T21:41:21.798522+00:00
-- url     : https://prove2.me/theorems/dd87cede-1f86-4ed1-952b-81b81d59721b
-- title:
--   Dobner's Lemma 3: a zero with a nonvanishing surrounding circle
-- statement:
--   Fix $t<0$, and let
--
--   $$
--   Z_t(s)=\sum_{n=1}^{\infty}\exp\!\left(\frac{t}{4}\log^2n\right)n^{-s}.
--   $$
--
--   There exist a center $c\in\mathbb C$, a radius $r>0$, and a constant $\delta>0$ such that
--
--   $$
--   Z_t(c)=0,
--   \qquad
--   \delta\leq |Z_t(s)|\quad\text{whenever }|s-c|=r.
--   $$
--
--   This combines the zero-existence conclusion of Dobner's Lemma 3 with the nonvanishing circle chosen in Section 3.1. The positive boundary margin allows the zero to persist under sufficiently small holomorphic perturbations.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Lemma 3: statement p. 15, proof p. 29; the choice of the circle and its positive minimum is in Section 3.1, p. 14. Specialized to F = zeta.

import Definitions.Def_DeBruijnNewman_Dobner
open Metric

theorem DeBruijnNewman.Dobner.zeta_zero_disk (t : ℝ) (ht : t < 0) :
    ∃ (c : ℂ) (r δ : ℝ), 0 < r ∧ 0 < δ ∧
      DeBruijnNewman.Dobner.zetaT t c = 0 ∧
      ∀ s ∈ sphere c r, δ ≤ ‖DeBruijnNewman.Dobner.zetaT t s‖ := by sorry
