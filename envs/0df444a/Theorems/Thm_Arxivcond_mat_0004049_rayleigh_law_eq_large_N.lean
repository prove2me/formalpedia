-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_rayleigh_law_eq_large_N
-- name    : Arxivcond_mat_0004049.rayleigh_law_eq_large_N
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T15:11:25.951849+00:00
-- url     : https://prove2.me/theorems/9c2ea430-1b0d-4feb-bb0e-a63ef496cdfc
-- title:
--   Rayleigh's law for $n = m$: $N I$ converges to the exponential law with mean $2$
-- statement:
--   Let $\gamma > 0$. For equal incident and detected modes ($n = m$), let
--
--   $$
--   I_N = |C_0|^2, \qquad C_0 = \sum_{i=1}^N u_i^2 ,
--   $$
--
--   be the reflected intensity in the localized-regime model with $N$ modes, where $u = g/\|g\|_2$ is the incident column for a complex Gaussian vector $g$. Then, as $N \to \infty$, the rescaled intensity $N I_N$ converges in distribution to the exponential law with mean $2$, whose density is
--
--   $$
--   \Theta(x)\, \tfrac12 e^{-x/2} .
--   $$
--
--   Equivalently, $P(I) \approx \tfrac12 N e^{-NI/2}$ at large $N$: the mean intensity in the incident mode is twice that in any other mode. This is the $n = m$ half of eq. (1), the static coherent backscattering effect.
--
--   **Formalization Note** Convergence in distribution is `LawTendsto` from the mission definitions file: expectations of bounded continuous test functions converge.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 1, eq. (1), case $n = m$

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem rayleigh_law_eq_large_N (γ : ℝ) (hγ : 0 < γ) :
    LawTendsto γ (fun N (ω : Sample N) => (N : ℝ) * intensityEq ω)
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x / 2) / 2 else 0))) := by sorry

end Arxivcond_mat_0004049
