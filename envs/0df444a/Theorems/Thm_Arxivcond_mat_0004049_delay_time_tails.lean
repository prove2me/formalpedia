-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_delay_time_tails
-- name    : Arxivcond_mat_0004049.delay_time_tails
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:14:06.015939+00:00
-- url     : https://prove2.me/theorems/63dd9a7a-8510-5c62-b949-9e5cf64a811a
-- title:
--   Eqs. (16)-(17): tails of the delay-time distributions
-- statement:
--   (i) Localized regime: let $\gamma>0$. In the localized-regime model with $n\ne m$, the law of $\varphi'/(\gamma N^{3/2})$ converges as $N\to\infty$ to a law with a continuous density $g\ge0$ whose tails decay as $|y|^{-2}$: there is $c>0$ with $y^2g(y)\to c$ as $y\to+\infty$ and as $y\to-\infty$.
--
--   (ii) Diffusive regime: for $Q,\bar\varphi'>0$ there is $c>0$ with $|\varphi'|^3P_{\rm diff}(\varphi')\to c$ as $\varphi'\to\pm\infty$.
--
--   **Formalization Note** The paper's $P(\varphi')$ is eq. (16) with the large-$N$ weight eq. (15). It is stated on the scale $\gamma N^{3/2}$ of the width of its peak (p. 3, $\Delta\varphi'\simeq\gamma N^{3/2}$), where the large-$N$ limit exists. Read literally at finite $N$, eq. (16) with eq. (15) integrates over the region $B_2<B_1^2$, where $B_2+\varphi'^2-2B_1\varphi'$ vanishes and the integral diverges.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c011; text after eq. (17), PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem delay_time_tails (γ : ℝ) (hγ : 0 < γ) :
    (∃ g : ℝ → ℝ, Continuous g ∧ (∀ y, 0 ≤ g y) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => delayNe ω / (γ * N * Real.sqrt N))
        ((volume : Measure ℝ).withDensity (fun y => ENNReal.ofReal (g y))) ∧
      ∃ c : ℝ, 0 < c ∧ Tendsto (fun y => y ^ 2 * g y) atTop (𝓝 c) ∧
        Tendsto (fun y => y ^ 2 * g y) atBot (𝓝 c)) ∧
    ∀ Q phibar : ℝ, 0 < Q → 0 < phibar → ∃ c : ℝ, 0 < c ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atTop (𝓝 c) ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atBot (𝓝 c) := by sorry

end Arxivcond_mat_0004049
