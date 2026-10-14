-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_truncatedSingularIntegral_sub_le
-- name    : DbarRegularity.eLpNorm_truncatedSingularIntegral_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T18:16:25.209284+00:00
-- url     : https://prove2.me/theorems/874e665b-ebdc-4d71-b8b3-e4ff21247bd0
-- title:
--   L^p Cauchy estimate for truncated singular integrals of compactly supported C^1 functions
-- statement:
--   Let $d\ge1$, $B\in\mathbb{R}$, and let $K:\mathbb{R}^d\to\mathbb{C}$ be measurable with
--   $$|K(x)|\le B|x|^{-d}\ (x\ne0),\qquad \int_{R_1<|x|<R_2}K(x)\,dx=0\ (0<R_1<R_2).$$
--   Let $1<p<\infty$, let $f:\mathbb{R}^d\to\mathbb{C}$ be $C^1$ with compact support, and put $T_\varepsilon f(x)=\int_{|y|\ge\varepsilon}f(x-y)K(y)\,dy$. Then there is a constant $C$ (depending on $f$, $K$, $p$) such that
--   $$\|T_\varepsilon f-T_\eta f\|_p\le C\,\eta\qquad\text{whenever }0<\varepsilon\le\eta\le1 .$$
--
--   In particular $(T_\varepsilon f)_{\varepsilon>0}$ is Cauchy in $L^p$ as $\varepsilon\to0$ for such $f$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`; $T_\varepsilon f$ is the Bochner integral `∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y`; $C^1$ is `ContDiff ℝ 1 f`, compact support is `HasCompactSupport f`. The bound reads `eLpNorm (T_ε f - T_η f) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C * η)`, with $C$ chosen before $\varepsilon,\eta$. No Hörmander condition is assumed.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- For a kernel with `|K(x)| ≤ B |x|^{-d}` and vanishing integrals over annuli, and a compactly
supported `C¹` function `f`, the truncated singular integrals satisfy
`‖T_ε f - T_η f‖_p ≤ C η` for `0 < ε ≤ η ≤ 1`, with `C` depending on `f` (and `K`, `p`). -/
theorem eLpNorm_truncatedSingularIntegral_sub_le {d : ℕ} (hd : 0 < d)
    (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε η : ℝ, 0 < ε → ε ≤ η → η ≤ 1 →
      eLpNorm ((fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) -
          (fun x => ∫ y in {y | η ≤ ‖y‖}, f (x - y) * K y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * η) := by sorry

end DbarRegularity
