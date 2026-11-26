-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_spectral_moment_scaling_and_divergent_means
-- name    : Arxivcond_mat_0004049.spectral_moment_scaling_and_divergent_means
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T20:11:27.903358+00:00
-- url     : https://prove2.me/theorems/d7de92b2-b3bd-4adb-a634-29a98358d6d2
-- title:
--   Eq. (15): most probable spectral moments and divergent means
-- statement:
--   Let $P(B_1,B_2)$ be the distribution of eq. (15), for $N\ge1$ and $\gamma>0$.
--
--   (i) The mean values diverge: $\int\!\!\int B_1P(B_1,B_2)\,dB_1dB_2=\infty$ and $\int\!\!\int B_2P(B_1,B_2)\,dB_1dB_2=\infty$.
--
--   (ii) The most probable values scale as $B_1\sim\gamma N$, $B_2\sim\gamma^2N^3$: there are constants $b_1,b_2>0$, independent of $N$ and $\gamma$, such that $(B_1,B_2)=(\gamma Nb_1,\gamma^2N^3b_2)$ is a global maximiser of $P(\cdot,\cdot)$ for every $N\ge1$ and $\gamma>0$.
--
--   **Formalization Note** "$\sim$" is read as: the location of the maximum is exactly $\gamma N$ and $\gamma^2N^3$ times fixed constants. The integrals in (i) are of the nonnegative parts.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c006; text after eq. (15), PDF p. 2

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem spectral_moment_scaling_and_divergent_means :
    (∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ →
      ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (B.1 * eq15Density N γ B.1 B.2) = ⊤ ∧
      ∫⁻ B : ℝ × ℝ, ENNReal.ofReal (B.2 * eq15Density N γ B.1 B.2) = ⊤) ∧
    ∃ b1 b2 : ℝ, 0 < b1 ∧ 0 < b2 ∧ ∀ N : ℕ, 1 ≤ N → ∀ γ : ℝ, 0 < γ → ∀ B1 B2 : ℝ,
      eq15Density N γ B1 B2 ≤ eq15Density N γ (γ * N * b1) (γ ^ 2 * (N : ℝ) ^ 3 * b2) := by sorry

end Arxivcond_mat_0004049
