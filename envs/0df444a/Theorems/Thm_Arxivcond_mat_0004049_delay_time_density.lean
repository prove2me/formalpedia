-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_delay_time_density
-- name    : Arxivcond_mat_0004049.delay_time_density
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:10:08.556398+00:00
-- url     : https://prove2.me/theorems/a81091da-8489-5243-8ae7-ee7a48c78e1e
-- title:
--   Eq. (16): distribution of the single-mode delay time
-- statement:
--   Let $N\ge2$ and $\gamma>0$, and consider the localized-regime model with $n\ne m$. Then the law of $\varphi'=\mathrm{Re}\,A_1/A_0$ has the density
--
--   $$P(\varphi')=\Big\langle\frac{B_2-B_1^2}{2(B_2+\varphi'^2-2B_1\varphi')^{3/2}}\Big\rangle=\int\!\!\int dB_1\,dB_2\,\frac{P(B_1,B_2)(B_2-B_1^2)}{2(B_2+\varphi'^2-2B_1\varphi')^{3/2}},$$
--
--   where $P(B_1,B_2)$ is the joint law of the spectral moments. This is $\int_0^\infty P(I,\varphi')\,dI$ of eq. (13).
--
--   **Formalization Note** The average is written as an integral over the model, which is the same as integrating against the law $P(B_1,B_2)$ of $(B_1,B_2)$. The large-$N$ form of that law, eq. (15), is the separate statement `spectral_moment_density_large_N`.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c007; eq. (16), PDF p. 2

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem delay_time_density (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (localizedModel N γ).map delayNe =
      (volume : Measure ℝ).withDensity (fun φ =>
        ∫⁻ ω, ENNReal.ofReal (eq16Kernel (specMoment 1 ω) (specMoment 2 ω) φ)
          ∂(localizedModel N γ)) := by sorry

end Arxivcond_mat_0004049
