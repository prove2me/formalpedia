-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_indicator_sub_le
-- name    : DbarRegularity.lintegral_indicator_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:36:35.842344+00:00
-- url     : https://prove2.me/theorems/fb1eeac5-36c1-4853-ad16-5b02267557ce
-- title:
--   Truncating a kernel at radius r changes its Hörmander integral by at most C·B
-- statement:
--   Let $d\ge1$. There is a constant $C\ge0$, depending only on $d$, with the following property. Let $K:\mathbb{R}^d\to\mathbb{C}$ and $B\in\mathbb{R}$ satisfy $|K(x)|\le B|x|^{-d}$ for $x\ne0$, let $r>0$, and let $K_r=K\,\mathbf 1_{\{|x|\ge r\}}$. Then for every $y\in\mathbb{R}^d$
--   $$\int_{|x|\ge2|y|}|K_r(x-y)-K_r(x)|\,dx\;\le\;\int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx+C\,B .$$
--
--   So the Hörmander condition $\int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx\le B$ passes to all truncations $K_r$ with a constant independent of $r$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`. Both integrals are lower Lebesgue integrals `∫⁻` of `‖·‖ₑ` over `{x | 2 * ‖y‖ ≤ ‖x‖}`, so no measurability of $K$ is needed; $C\,B$ enters as `ENNReal.ofReal (C * B)`. $C$ is chosen before $K$, $B$, $r$, $y$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- Truncating a kernel with `|K(x)| ≤ B |x|^{-d}` to `{|x| ≥ r}` changes its Hörmander integral
`∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx` by at most `C B`, with `C` depending only on `d`. -/
theorem lintegral_indicator_sub_le {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ),
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) → ∀ r : ℝ, 0 < r → ∀ y : EuclideanSpace ℝ (Fin d),
        ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖},
            ‖{x | r ≤ ‖x‖}.indicator K (x - y) - {x | r ≤ ‖x‖}.indicator K x‖ₑ ≤
          (∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ) + ENNReal.ofReal (C * B) := by sorry

end DbarRegularity
