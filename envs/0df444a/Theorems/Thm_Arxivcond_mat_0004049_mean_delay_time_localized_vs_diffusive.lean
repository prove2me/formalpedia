-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_mean_delay_time_localized_vs_diffusive
-- name    : Arxivcond_mat_0004049.mean_delay_time_localized_vs_diffusive
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T20:12:17.833912+00:00
-- url     : https://prove2.me/theorems/4815ed43-cf6f-4927-b6b0-8ee8894b301b
-- title:
--   Eqs. (16)-(17): the mean delay time diverges in the localized regime and equals the diffusive mean
-- statement:
--   (i) Localized regime: for every $N\ge1$ and $\gamma>0$, in the localized-regime model with $n\ne m$ the mean of the single-mode delay time diverges, $\langle|\varphi'|\rangle=\infty$, and so does $\langle B_1\rangle=\infty$.
--
--   (ii) Diffusive regime: for $Q>0$ and $\bar\varphi'>0$, the distribution $P_{\rm diff}(\varphi')=(Q/2\bar\varphi')[Q+(\varphi'/\bar\varphi'-1)^2]^{-3/2}$ of eq. (17) has a finite mean, equal to $\bar\varphi'$:
--
--   $$\int_{-\infty}^\infty\varphi'P_{\rm diff}(\varphi')\,d\varphi'=\bar\varphi'.$$
--
--   **Formalization Note** "$\langle\varphi'\rangle$ diverges" is stated as $\langle|\varphi'|\rangle=\infty$, so that $\varphi'$ is not integrable. The identity $\langle\varphi'\rangle=\langle B_1\rangle$ is reflected by stating that both are infinite.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c010; text after eq. (17), PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem mean_delay_time_localized_vs_diffusive :
    (∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ →
      ∫⁻ ω, ENNReal.ofReal |delayNe ω| ∂(localizedModel N γ) = ⊤ ∧
      ∫⁻ ω, ENNReal.ofReal (specMoment 1 ω) ∂(localizedModel N γ) = ⊤) ∧
    ∀ Q phibar : ℝ, 0 < Q → 0 < phibar →
      Integrable (fun φ : ℝ => φ * pDiff Q phibar φ) ∧
      ∫ φ : ℝ, φ * pDiff Q phibar φ = phibar := by sorry

end Arxivcond_mat_0004049
