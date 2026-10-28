-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_hoeffding_inequality
-- name    : ClusterSim.EdgeCut.hoeffding_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:27.135627+00:00
-- url     : https://prove2.me/theorems/9c253632-d0ea-4fab-8241-92194c48f9dc
-- title:
--   Hoeffding's inequality (p. 9) — Pr[|X̄ − E X̄| < δ] ≥ 1 − 2exp(−Nδ²/2a²) > 2/3 when N ≥ 4a²/δ²
-- statement:
--   Let $X_1,\dots,X_N$ ($N\ge1$) be i.i.d. real random variables with common law $\mu$ such that $|X_i|\le a$ almost surely, where $a>0$, and let $\bar X=(X_1+\dots+X_N)/N$. Then for every $\delta>0$,
--   $$\Pr\big[\,|\bar X-\mathbb E[\bar X]|<\delta\,\big]\ \ge\ 1-2\exp\Big(-\frac{N\delta^2}{2a^2}\Big),$$
--   and the right-hand side exceeds $2/3$ whenever $N\ge 4a^2/\delta^2$.
--
--   The paper states this form of Hoeffding's inequality "for the sake of reference" and uses it to choose the number of samples of the simulation. The first inequality is the two-sided Hoeffding bound for sums with range $[-a,a]$ (the referenced item `Concentration.hoeffding_two_sided`, with deviation $N\delta$); the second is the numerical fact $1-2e^{-2}>2/3$.
--
--   **Formalization Note** The $N$ samples are the coordinates of the product measure $\mu^{\otimes N}$ on $\mathbb R^N$, and $\mathbb E[\bar X]=\int t\,d\mu(t)$. The bound on $|X_i|$ makes the integral finite.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 9, Hoeffding's inequality (Supplemental Material, between §III and §IV; from ref. [54])

import Mathlib

namespace ClusterSim.EdgeCut

open MeasureTheory

/-- Hoeffding's inequality as stated on p. 9 (from [54]): for `N ≥ 1` i.i.d. real random variables
with law `μ` and `|X_i| ≤ a` almost surely, the average `X̄ = (X_1 + ⋯ + X_N)/N` satisfies
`Pr[|X̄ − E[X̄]| < δ] ≥ 1 − 2 exp(−Nδ²/2a²)`, and `1 − 2 exp(−Nδ²/2a²) > 2/3` when `N ≥ 4a²/δ²`.
The `N` samples are the coordinates of the product measure `μ^{⊗N}` on `Fin N → ℝ`. -/
theorem hoeffding_inequality (μ : Measure ℝ) [IsProbabilityMeasure μ] {a δ : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ a) (N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal (1 - 2 * Real.exp (-(N * δ ^ 2) / (2 * a ^ 2))) ≤
        Measure.pi (fun _ : Fin N => μ)
          {x | |(∑ i, x i) / N - ∫ t, t ∂μ| < δ} ∧
      (4 * a ^ 2 / δ ^ 2 ≤ N → (2 / 3 : ℝ) < 1 - 2 * Real.exp (-(N * δ ^ 2) / (2 * a ^ 2))) := by sorry

end ClusterSim.EdgeCut
