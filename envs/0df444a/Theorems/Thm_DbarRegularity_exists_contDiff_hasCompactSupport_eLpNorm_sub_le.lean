-- Prove2me | Theorems.Thm_DbarRegularity_exists_contDiff_hasCompactSupport_eLpNorm_sub_le
-- name    : DbarRegularity.exists_contDiff_hasCompactSupport_eLpNorm_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T18:11:50.871483+00:00
-- url     : https://prove2.me/theorems/ef0ec73d-83a9-4e0e-b2ba-be89be7c7394
-- title:
--   Smooth compactly supported functions are dense in L^p(R^d), 1 ≤ p < ∞
-- statement:
--   Let $d\ge0$ and $1\le p<\infty$. For every $f\in L^p(\mathbb{R}^d;\mathbb{C})$ and every $\delta>0$ there is a $C^\infty$ function $h:\mathbb{R}^d\to\mathbb{C}$ with compact support such that $\|f-h\|_p\le\delta$.
--
--   So smooth compactly supported functions are dense in $L^p(\mathbb{R}^d)$ for $1\le p<\infty$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`; $p$ is in `ℝ≥0∞` with `1 ≤ p` and `p ≠ ∞`. Smoothness is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h` (i.e. $C^\infty$, not analytic), compact support is `HasCompactSupport h`, and the error is `eLpNorm (f - h) p volume ≤ ENNReal.ofReal δ`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set Metric ContinuousLinearMap
open scoped ENNReal Convolution

/-- Smooth compactly supported functions are dense in `L^p(ℝ^d; ℂ)`, `1 ≤ p < ∞`. -/
theorem exists_contDiff_hasCompactSupport_eLpNorm_sub_le {d : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MemLp f p volume) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ HasCompactSupport h ∧
      eLpNorm (f - h) p volume ≤ ENNReal.ofReal δ := by sorry

end DbarRegularity
