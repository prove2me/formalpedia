-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_spectral_moment_density_large_N
-- name    : Arxivcond_mat_0004049.spectral_moment_density_large_N
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:10:42.916423+00:00
-- url     : https://prove2.me/theorems/906e5a87-5bd3-5a9c-b25d-5ad4fd074366
-- title:
--   Eq. (15): joint distribution of the spectral moments in the large-N limit
-- statement:
--   Let $\gamma>0$. In the localized-regime model, as $N\to\infty$ the joint law of the spectral moments $B_1=\sum_i|u_i|^2\tau_i$, $B_2=\sum_i|u_i|^2\tau_i^2$ is given by eq. (15),
--
--   $$P(B_1,B_2)=\Theta(B_1)\Theta(B_2)e^{-NB_1^2/B_2}\Big[\frac{B_1^2\gamma N^3}{B_2^4}(B_2+\gamma N^2B_1)e^{-2\gamma N/B_1}-\frac{\gamma^3N^5}{4B_2^5}(2B_2^2-4B_1^2B_2N+B_1^4N^2)\,\mathrm{Ei}\Big(-\frac{2\gamma N}{B_1}\Big)\Big],$$
--
--   in the following sense: for every bounded continuous $f$ on $\mathbb{R}^2$,
--
--   $$E_N\,f\Big(\frac{B_1}{\gamma N},\frac{B_2}{\gamma^2N^3}\Big)-\int\!\!\int f\Big(\frac{B_1}{\gamma N},\frac{B_2}{\gamma^2N^3}\Big)P(B_1,B_2)\,dB_1\,dB_2\to0.$$
--
--   **Formalization Note** "Exact in the large-$N$ limit" is stated as convergence in law on the scale of the most probable values, $B_1\sim\gamma N$, $B_2\sim\gamma^2N^3$. On this scale eq. (15) does not depend on $N$: with $B_1=\gamma Nb_1$, $B_2=\gamma^2N^3b_2$ it becomes the density $e^{-b_1^2/b_2}\big[b_1^2(b_1+b_2)b_2^{-4}e^{-2/b_1}-\tfrac14(2b_2^2-4b_1^2b_2+b_1^4)b_2^{-5}\mathrm{Ei}(-2/b_1)\big]$. The claim records $u$ as Gaussian with variance $1/N$, the paper's large-$N$ form of a Haar column; the model uses the exact column $u=g/\|g\|_2$, which differs from $g$ by the factor $\|g\|_2^{-1}\to1$.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c005; eq. (15), PDF p. 2

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem spectral_moment_density_large_N (γ : ℝ) (hγ : 0 < γ)
    (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) :
    Tendsto (fun N : ℕ =>
      (∫ ω, f (specMoment 1 ω / (γ * N), specMoment 2 ω / (γ ^ 2 * (N : ℝ) ^ 3))
          ∂(localizedModel N γ)) -
        ∫ B : ℝ × ℝ, f (B.1 / (γ * N), B.2 / (γ ^ 2 * (N : ℝ) ^ 3)) * eq15Density N γ B.1 B.2)
      atTop (𝓝 0) := by sorry

end Arxivcond_mat_0004049
