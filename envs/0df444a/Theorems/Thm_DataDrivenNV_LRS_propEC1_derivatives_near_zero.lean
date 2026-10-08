-- Prove2me | Theorems.Thm_DataDrivenNV_LRS_propEC1_derivatives_near_zero
-- name    : DataDrivenNV.LRS.propEC1_derivatives_near_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:26.864367+00:00
-- url     : https://prove2.me/theorems/4dfe6c21-2823-4e64-87cd-1a007f0c4e3a
-- title:
--   Proposition EC.1, p. ec5 — Pr(∂₋C(Q̂_N) ≤ γ and ∂₊C(Q̂_N) ≥ −γ) ≥ 1 − 2exp(−3Nγ²/(6bh + 8γ(b+h)))
-- statement:
--   Let $D$ have law $\mu$ on $\mathbb R$ with cdf $F$, let $b,h>0$, and let $\hat Q_N$ be the $b/(b+h)$ quantile of an i.i.d. sample $D^1,\dots,D^N$ ($N\ge1$) from $\mu$. Let $\partial_+C(q)=-b+(b+h)F(q)$ and $\partial_-C(q)=-b+(b+h)\Pr(D<q)$. Then for every $\gamma>0$,
--   $$\Pr\big(\partial_-C(\hat Q_N)\le\gamma \text{ and } \partial_+C(\hat Q_N)\ge-\gamma\big) \ \ge\ 1-2\exp\Big(\frac{-3N\gamma^2}{6bh+8\gamma(b+h)}\Big).$$
--
--   The result holds for every demand distribution, with no density, continuity or moment assumption. It says that the sample quantile lands, with high probability, where both one-sided derivatives of the expected cost are close to zero, i.e. near the true critical quantile.
--
--   **Formalization Note** The statement bounds the probability of the complementary (failure) event under the product measure $\mu^{\otimes N}$ by $2\exp(\cdot)$. The derivatives enter through their formulas in terms of $F$ and $\Pr(D<\cdot)$, so no integrability of $D$ is assumed.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. ec5, Proposition EC.1 (proof pp. ec5–ec6)

import Mathlib
import Definitions.Def_DataDrivenNV_LRS_Setting

open MeasureTheory ProbabilityTheory

namespace DataDrivenNV.LRS

/-- Proposition EC.1, p. ec5. For an i.i.d. sample of size `N ≥ 1` from the demand law `μ` and
every `γ > 0`, the SAA quantile `Q̂_N` satisfies `∂₋C(Q̂_N) ≤ γ` and `∂₊C(Q̂_N) ≥ -γ` except on
an event of probability at most `2 exp(-3Nγ² / (6bh + 8γ(b + h)))`. -/
theorem propEC1_derivatives_near_zero (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (Measure.pi fun _ : Fin N => μ)
        {x : Fin N → ℝ | ¬ (dMinus μ b h (saaQuantile b h x) ≤ γ ∧
          -γ ≤ dPlus μ b h (saaQuantile b h x))} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(3 * (N : ℝ) * γ ^ 2) / (6 * b * h + 8 * γ * (b + h)))) := by sorry

end DataDrivenNV.LRS
