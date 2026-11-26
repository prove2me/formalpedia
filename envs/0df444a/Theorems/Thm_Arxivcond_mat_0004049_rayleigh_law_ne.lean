-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_rayleigh_law_ne
-- name    : Arxivcond_mat_0004049.rayleigh_law_ne
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T15:11:33.390419+00:00
-- url     : https://prove2.me/theorems/c41d0d72-6006-4332-bd19-3ad7e64e2725
-- title:
--   Rayleigh's law for $n \ne m$: $P(I) = N e^{-NI}$ exactly, for every $N \ge 1$
-- statement:
--   Let $\gamma > 0$ and $N \ge 1$. In the localized-regime model, the reflected intensity into a mode different from the incident one,
--
--   $$
--   I = |A_0|^2, \qquad A_0 = \sum_{i=1}^N u_i v_i ,
--   $$
--
--   has the exponential distribution with rate $N$:
--
--   $$
--   P(I) = \Theta(I)\, N e^{-N I} .
--   $$
--
--   The model is that of the paper: the rates $\mu_i = 1/\tau_i$ follow the Laguerre ensemble of eq. (7), the incident column is $u = g/\|g\|_2$ for a complex Gaussian vector $g$, and the detected column $v$ is an independent complex Gaussian vector with entries of variance $1/N$.
--
--   This is the $n \ne m$ half of eq. (1) (Rayleigh's law), and it holds exactly at every $N$, not only for large $N$.
--
--   **Formalization Note** The statement is an equality of measures on $\mathbb{R}$: the pushforward of `localizedModel N γ` under `intensityNe` equals Lebesgue measure with density $\mathbf{1}_{I>0} N e^{-NI}$.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 1, eq. (1), case $n \ne m$

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem rayleigh_law_ne (γ : ℝ) (hγ : 0 < γ) :
    ∀ N : ℕ, 1 ≤ N → (localizedModel N γ).map intensityNe =
      (volume : Measure ℝ).withDensity
        (fun I => ENNReal.ofReal (if 0 < I then (N : ℝ) * Real.exp (-(N : ℝ) * I) else 0)) := by sorry

end Arxivcond_mat_0004049
