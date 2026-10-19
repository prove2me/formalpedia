-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_lemma_3
-- name    : ConfoundRobust.Minimax.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:04.330742+00:00
-- url     : https://prove2.me/theorems/7cf72501-b20f-46c2-80cc-95bcff3ed3bd
-- title:
--   Lemma 3, p. 40 — for fixed π, uniform deviation of u(Y(π(T|X) − π₀(T|X))) over monotone u ≤ 9√(2π log(1/p)/n), p ≤ 1/2
-- statement:
--   Let $\mu$ be the law of $(X,T,Y)$, let $\pi$ and $\pi_0$ be fixed policies, $n \ge 1$, and $p \in (0, 1/2]$. With probability at least $1-p$ over an iid sample of size $n$,
--   $$\sup_{u} \frac1n \Big| \sum_{i=1}^n u\big(Y_i(\pi(T_i\mid X_i) - \pi_0(T_i\mid X_i))\big) - \mathbb E\big[u\big(Y(\pi(T\mid X) - \pi_0(T\mid X))\big)\big] \Big| \le 9 \sqrt{\frac{2\pi \log(1/p)}{n}},$$
--   the supremum over all nondecreasing $u : \mathbb R \to [0,1]$ (the class $\mathcal U^\Gamma(\pi)$). Here $\pi$ in $2\pi$ is the number $3.14159\ldots$
--
--   This controls the weight part of the regret decomposition for one policy at a time; it is a Glivenko–Cantelli bound for the monotone transformations of the score.
--
--   **Formalization Note** The page states Lemma 3 for every $p$; it is false for $p$ close to $1$ (the class contains the indicators $\mathbb 1\{s > c\}$, so the left side is at least the Kolmogorov–Smirnov distance, whose small quantiles are much smaller than the bound for $p \to 1$). For $p \le 1/2$ it follows from the Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant, and the theorem is posed for $p \in (0, 1/2]$, which covers every use in the paper. "With probability at least $1-p$" is a measurable event of product measure $\ge 1-p$ on which the bound holds for every $u$.
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Lemma 3, Appendix B.1, p. 40 (𝒰^Γ(π) defined on p. 38)

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem lemma_3 {𝒳 : Type} [MeasurableSpace 𝒳] (m n : ℕ) (hn : 0 < n)
    (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
    (π π0 : 𝒳 → Fin m → ℝ) (hπ : IsPolicy π) (hπ0 : IsPolicy π0)
    (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    ∃ E : Set (Fin n → Obs 𝒳 m), MeasurableSet E ∧
      ENNReal.ofReal (1 - p) ≤ Measure.pi (fun _ : Fin n => μ) E ∧
      ∀ ω ∈ E, ∀ u : ℝ → ℝ, IsUnitMonotone u →
        |(n : ℝ)⁻¹ * ∑ i, u (score π π0 (ω i)) - ∫ z, u (score π π0 z) ∂μ| ≤
          9 * Real.sqrt (2 * Real.pi * Real.log (1 / p) / n) := by sorry

end ConfoundRobust.Minimax
