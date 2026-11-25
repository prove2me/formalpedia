-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_joint_intensity_delay_density
-- name    : Arxivcond_mat_0004049.joint_intensity_delay_density
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:09:46.057941+00:00
-- url     : https://prove2.me/theorems/8709e326-46ed-423b-8945-6b5ce7e9ab02
-- title:
--   Eq. (13): joint distribution of intensity and single-mode delay time
-- statement:
--   Let $N\ge2$ and $\gamma>0$, and consider the localized-regime model with $n\ne m$. Then the joint law of the reflected intensity $I=|A_0|^2$ and the single-mode delay time $\varphi'=\mathrm{Re}\,A_1/A_0$ has the density
--
--   $$P(I,\varphi')=\Theta(I)\Big(\frac{N^3I}{\pi}\Big)^{1/2}e^{-NI}\Big\langle(B_2-B_1^2)^{-1/2}\exp\Big(-NI\frac{(\varphi'-B_1)^2}{B_2-B_1^2}\Big)\Big\rangle$$
--
--   with respect to Lebesgue measure on $\mathbb{R}^2$. The average is over $u$ and the delay times $\tau_i$ through the spectral moments $B_k=\sum_i|u_i|^2\tau_i^k$.
--
--   **Formalization Note** $N\ge2$ is needed: for $N=1$, $B_2=B_1^2$ and $\varphi'=\tau_1$ has no joint density with $I$. For $N\ge2$, $B_2>B_1^2$ almost surely.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c002; eqs. (8)-(13), PDF p. 2

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem joint_intensity_delay_density (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (localizedModel N γ).map (fun ω => (intensityNe ω, delayNe ω)) =
      (volume : Measure (ℝ × ℝ)).withDensity (fun q =>
        ∫⁻ ω, ENNReal.ofReal (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2)
          ∂(localizedModel N γ)) := by sorry

end Arxivcond_mat_0004049
