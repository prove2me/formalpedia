-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_lemma_3_2
-- name    : CalibratedMA.Randomized.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:31.05998+00:00
-- url     : https://prove2.me/theorems/f7c055bc-e853-4a1c-b609-8b00db053572
-- title:
--   Lemma 3.2 — lifted rounded tests are linear interpolants
-- statement:
--   Fix a grid partition $\Gamma=(\gamma_0,\dots,\gamma_M)$ and a test $h:\{\gamma_0,\dots,\gamma_M\}\to\mathbb R$. Let $P=\mathrm{Round}_\Gamma(S)$ and $a_h(s)=\mathbb E[h(P)\mid S=s]$. Then, for $0\le j<M$ and $s\in[\gamma_j,\gamma_{j+1}]$,
--   $$a_h(s)=h(\gamma_j)\frac{\gamma_{j+1}-s}{\gamma_{j+1}-\gamma_j}+h(\gamma_{j+1})\frac{s-\gamma_j}{\gamma_{j+1}-\gamma_j}.$$
--   Thus $a_h$ is the continuous piecewise-linear interpolation of the values $h(\gamma_j)$ on the partition points.
--
--   The lemma identifies the lifted tests in $\mathcal A_{M,\rho}$ as piecewise-linear functions of the score, which are continuous, as Lemma 3.1 requires.
--
--   **Formalization Note.** $a_h(s)$ is `liftTest M γ h s`, the integral of $h$ against the law of $\mathrm{Round}_\Gamma(s)$. The test is a function $h:\mathbb R\to\mathbb R$, of which only the values at the partition points enter. "Continuous piecewise-linear interpolation" is stated as the interval formula together with continuity on $[0,1]$.
--
--   Differences from the source:
--   - encoding: $a_h(s)=\mathbb E[h(P)\mid S=s]$ → the integral of $h$ against the law of $\mathrm{Round}_\Gamma(s)$; reason: given $S=s$, $P$ has exactly this law.
--   - encoding: $h$ on the partition points → $h:\mathbb R\to\mathbb R$; reason: only values at partition points enter.
--   - encoding: a grid increment ρ > 0 with integer 1/ρ → a natural grid denominator K with ρ = 1/K, enforced by IsGridPartition; reason: a valid partition forces K ≥ 1 and represents every source grid.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 14, Lemma 3.2

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Rounding

open MeasureTheory

namespace CalibratedMA.Randomized

/-- Lemma 3.2 (p. 14): the lift `a_h(s) = E[h(Round_Γ(s))]` of a test `h` on the partition
points is the linear interpolation of the values `h(γ_j)` on each interval `[γ_j, γ_{j+1}]`,
and it is continuous on `[0,1]`. -/
theorem lemma_3_2 (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (h : ℝ → ℝ) :
    (∀ j < M, ∀ s ∈ Set.Icc (γ j) (γ (j + 1)),
      liftTest M γ h s =
        h (γ j) * ((γ (j + 1) - s) / (γ (j + 1) - γ j)) +
          h (γ (j + 1)) * ((s - γ j) / (γ (j + 1) - γ j))) ∧
    ContinuousOn (liftTest M γ h) (Set.Icc (0 : ℝ) 1) := by sorry

end CalibratedMA.Randomized
