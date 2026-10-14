-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_inv_norm_pow_succ_le
-- name    : DbarRegularity.lintegral_inv_norm_pow_succ_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:46:24.796989+00:00
-- url     : https://prove2.me/theorems/daecd9d2-3bed-4245-8192-f41f26037ebe
-- title:
--   Tail bound $\int_{|x|\ge R}|x|^{-(d+1)}\,dx\le C_d/R$ in $\mathbb R^d$
-- statement:
--   Let $d\ge 0$. There is a constant $C$, depending only on $d$, such that for every $R>0$
--   $$\int_{\{x\in\mathbb R^d:\ |x|\ge R\}}\frac{dx}{|x|^{d+1}}\;\le\;\frac{C}{R}.$$
--
--   This is the scale-invariant decay of the tail of $|x|^{-(d+1)}$, the integrability exponent one above the dimension; it is the basic size estimate for kernels whose gradient decays like $|x|^{-(d+1)}$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The integrand is written as `ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹)` and the integral is the lower Lebesgue integral `∫⁻` over the set `{x | R ≤ ‖x‖}`; the bound is `ENNReal.ofReal (C / R)` with a real constant `C` chosen before `R`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- In `ℝ^d`, the tail integral of `|x|^{-(d+1)}` over `{|x| ≥ R}` is bounded by `C / R`, with a
constant `C` depending only on `d`. -/
theorem lintegral_inv_norm_pow_succ_le (d : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      ∫⁻ x in {x : EuclideanSpace ℝ (Fin d) | R ≤ ‖x‖}, ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹)
        ≤ ENNReal.ofReal (C / R) := by sorry

end DbarRegularity
