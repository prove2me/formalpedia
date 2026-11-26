-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_delay_time_tails_localized
-- name    : Arxivcond_mat_0004049.delay_time_tails_localized
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T13:57:55.07729+00:00
-- url     : https://prove2.me/theorems/ebe94f51-bb6e-44a8-a5c8-6773aa4ca0d4
-- title:
--   Localized regime: the limiting delay-time density has $|\varphi'|^{-2}$ tails
-- statement:
--   Let $\gamma > 0$. For different incident and detected modes ($n \ne m$), let $\varphi'_N = \operatorname{Re}(A_1/A_0)$ be the single-mode delay time of eq. (6) in the localized-regime model with $N$ modes. Then there is a continuous, nonnegative function $g$ such that:
--
--   1. the rescaled delay time $\varphi'_N/(\gamma N^{3/2})$ converges in distribution as $N \to \infty$ to the law with density $g$;
--   2. both tails of $g$ decay as $y^{-2}$ with a common constant $c > 0$:
--
--   $$
--   \lim_{y \to +\infty} y^2 g(y) = \lim_{y \to -\infty} y^2 g(y) = c .
--   $$
--
--   The model is that of the paper: the rates $\mu_i = 1/\tau_i$ follow the Laguerre ensemble of eq. (7), the incident column is $u = g_0/\|g_0\|_2$ for a complex Gaussian vector $g_0$, and the detected column $v$ is an independent complex Gaussian vector with entries of variance $1/N$. The scale $\gamma N^{3/2}$ is the peak width of $P(\varphi')$ identified in the paper.
--
--   This is the localized half of the statement "In the tails $P$ decays $\propto |\varphi'|^{-2}$, while $P_{\rm diff} \propto |\varphi'|^{-3}$".
--
--   **Formalization Note** Convergence in distribution is `LawTendsto` from the mission definitions file: expectations of bounded continuous test functions converge.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 3, eqs. (16)-(17) and the sentence "In the tails $P$ decays $\propto |\varphi'|^{-2}$, while $P_{\rm diff} \propto |\varphi'|^{-3}$"

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem delay_time_tails_localized (γ : ℝ) (hγ : 0 < γ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ y, 0 ≤ g y) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => delayNe ω / (γ * N * Real.sqrt N))
        ((volume : Measure ℝ).withDensity (fun y => ENNReal.ofReal (g y))) ∧
      ∃ c : ℝ, 0 < c ∧ Tendsto (fun y => y ^ 2 * g y) atTop (𝓝 c) ∧
        Tendsto (fun y => y ^ 2 * g y) atBot (𝓝 c) := by sorry

end Arxivcond_mat_0004049
