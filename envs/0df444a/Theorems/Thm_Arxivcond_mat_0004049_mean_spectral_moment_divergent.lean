-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_mean_spectral_moment_divergent
-- name    : Arxivcond_mat_0004049.mean_spectral_moment_divergent
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T13:57:59.973061+00:00
-- url     : https://prove2.me/theorems/b3777580-4363-404a-89f3-56a193f2503c
-- title:
--   In the localized regime the mean spectral moment $\langle B_1\rangle$ diverges
-- statement:
--   Let $N \ge 1$ and $\gamma > 0$. The first spectral moment of eq. (11),
--
--   $$
--   B_1 = \sum_{i=1}^N |u_i|^2\, \tau_i ,
--   $$
--
--   has infinite mean:
--
--   $$
--   \langle B_1 \rangle = \infty .
--   $$
--
--   Here $\langle\cdot\rangle$ is the expectation in the localized-regime model of the paper at a fixed number of modes $N \ge 1$ and parameter $\gamma > 0$: the rates $\mu_i = 1/\tau_i$ follow the Laguerre ensemble of eq. (7), the incident column is $u = g/\|g\|_2$ for a complex Gaussian vector $g$, and the detected column $v$ is an independent complex Gaussian vector with entries of variance $1/N$.
--
--   The divergence comes from the heavy tail of the Laguerre ensemble at small rates $\mu_i$. The paper uses it to explain why the mean single-mode delay time $\langle\varphi'\rangle = \langle B_1\rangle$ diverges in the localized regime.
--
--   **Formalization Note** $B_1$ is `specMoment 1`, nonnegative since $\tau_i > 0$ almost surely; the mean is the lower Lebesgue integral of `ENNReal.ofReal (specMoment 1 ω)` under `localizedModel N γ`.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 3, text after eq. (15) ("the mean values $\langle B_1\rangle, \langle B_2\rangle$ diverge") and after eq. (17) ("the mean $\langle\varphi'\rangle = \langle B_1\rangle$ diverges for $P$")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem mean_spectral_moment_divergent (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ ω, ENNReal.ofReal (specMoment 1 ω) ∂(localizedModel N γ) = ⊤ := by sorry

end Arxivcond_mat_0004049
