-- Prove2me | Theorems.Thm_DbarRegularity_truncatedSingularIntegral_uniform_bound
-- name    : DbarRegularity.truncatedSingularIntegral_uniform_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T18:11:42.324305+00:00
-- url     : https://prove2.me/theorems/f159e698-cace-4f72-99b0-cba303dd44c7
-- title:
--   Uniform L^p bound for truncated singular integrals in dimension d ≥ 1
-- statement:
--   Let $d\ge1$, $B\in\mathbb{R}$, and let $K:\mathbb{R}^d\to\mathbb{C}$ be measurable with
--   $$|K(x)|\le B|x|^{-d}\ (x\ne0),\qquad \int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx\le B\ (y\ne0),\qquad \int_{R_1<|x|<R_2}K(x)\,dx=0\ (0<R_1<R_2).$$
--   Let $1<p<\infty$ and for $f\in L^p(\mathbb{R}^d)$, $\varepsilon>0$ put $T_\varepsilon f(x)=\int_{|y|\ge\varepsilon}f(x-y)K(y)\,dy$. Then there is a constant $A$, independent of $f$ and $\varepsilon$, with
--   $$\|T_\varepsilon f\|_p\le A\|f\|_p\qquad\text{for all }\varepsilon>0\text{ and }f\in L^p(\mathbb{R}^d).$$
--
--   This is inequality (21) of Stein's Theorem 2 (Ch. II §3.2) in positive dimension.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`; $T_\varepsilon f$ is the Bochner integral `∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y`. The second condition is a lower Lebesgue integral `∫⁻` bounded by `ENNReal.ofReal B`. `A : ℝ≥0` is chosen before $\varepsilon$ and $f$; the exponent is `ENNReal.ofReal p`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, Theorem 2, inequality (21), p. 35

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace DbarRegularity

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- Uniform `L^p` bound for the truncated singular integrals of a kernel satisfying Stein's
conditions (18)–(19), on all of `L^p`, `1 < p < ∞`, `d ≥ 1`. -/
theorem truncatedSingularIntegral_uniform_bound {d : ℕ} (hd : 0 < d)
    (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
