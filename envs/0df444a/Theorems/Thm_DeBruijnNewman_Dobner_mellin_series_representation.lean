-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_mellin_series_representation
-- name    : DeBruijnNewman.Dobner.mellin_series_representation
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T22:34:34.450086+00:00
-- url     : https://prove2.me/theorems/7d4b04f4-1804-4fe7-933f-542a7e7b59b7
-- title:
--   Dobner's Gaussian–Mellin series represents the canonical heat deformation
-- statement:
--   Fix $t<0$ and $s\in\mathbb C$. With $B_{t,N}$ the explicit Gaussian–Mellin integral on $\operatorname{Re}z=2$,
--
--   $$
--   \sum_{N=1}^{\infty}B_{t,N}(s)=\xi_t(J_t(s)),
--   \qquad
--   \xi_t(w)=8H_t(-i(2w-1)).
--   $$
--
--   This identity connects the individual contour coefficients to the canonical heat flow $H_t$. The normalization $\xi_t(w)=8H_t(-i(2w-1))$ is the existing one, matching the paper's full Fourier integral and its choice of theta kernel.
--
--   **Formalization Note.** The equality is expressed as `HasSum`, which includes convergence of the series. The natural-number index $n$ represents the positive integer $N=n+1$.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Section 3, equation (9), p. 12; Section 4, the convergent-sum identity preceding equation (17), p. 15. Includes the factor-eight conversion to the canonical platform H.

import Definitions.Def_DeBruijnNewman_Dobner_Mellin

theorem DeBruijnNewman.Dobner.mellin_series_representation (t : ℝ) (ht : t < 0) (s : ℂ) :
    HasSum (fun n : ℕ => DeBruijnNewman.Dobner.mellinTerm t s n)
      (DeBruijnNewman.Dobner.xiT t (DeBruijnNewman.Dobner.J t s)) := by sorry
