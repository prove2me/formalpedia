-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_mean_abs_delay_divergent
-- name    : Arxivcond_mat_0004049.mean_abs_delay_divergent
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T13:57:54.304647+00:00
-- url     : https://prove2.me/theorems/d4b08901-401e-5828-8f36-2825467fcb99
-- title:
--   In the localized regime the single-mode delay time has $\langle|\varphi'|\rangle = \infty$
-- statement:
--   Let $N \ge 1$ and $\gamma > 0$. For different incident and detected modes ($n \ne m$) the single-mode delay time of eq. (6),
--
--   $$
--   \varphi' = \operatorname{Re}\frac{A_1}{A_0}, \qquad A_k = \sum_{i=1}^N \tau_i^k\, u_i v_i ,
--   $$
--
--   is not integrable:
--
--   $$
--   \langle |\varphi'| \rangle = \infty .
--   $$
--
--   Here $\langle\cdot\rangle$ is the expectation in the localized-regime model of the paper at a fixed number of modes $N \ge 1$ and parameter $\gamma > 0$: the rates $\mu_i = 1/\tau_i$ follow the Laguerre ensemble of eq. (7), the incident column is $u = g/\|g\|_2$ for a complex Gaussian vector $g$, and the detected column $v$ is an independent complex Gaussian vector with entries of variance $1/N$.
--
--   This is the localized half of the paper's contrast between the regimes: the mean delay time diverges for the localized distribution $P$ of eq. (16), but is finite for the diffusion-theory distribution $P_{\rm diff}$ of eq. (17).
--
--   **Formalization Note** $\varphi'$ is `delayNe`, and the statement is the lower Lebesgue integral of $|\varphi'|$ under `localizedModel N γ`. With Lean's convention $z/0 = 0$, the value of $\varphi'$ on the null event $A_0 = 0$ is $0$.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 3, eq. (16) and the paragraph after eq. (17) ("the mean $\langle\varphi'\rangle = \langle B_1\rangle$ diverges for $P$")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem mean_abs_delay_divergent (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ ω, ENNReal.ofReal |delayNe ω| ∂(localizedModel N γ) = ⊤ := by sorry

end Arxivcond_mat_0004049
