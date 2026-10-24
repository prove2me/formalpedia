-- Prove2me | Theorems.Thm_FiniteEnergyPlane_monotoneOn_exp_mul_div_sq
-- name    : FiniteEnergyPlane.monotoneOn_exp_mul_div_sq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:06:26.196856+00:00
-- url     : https://prove2.me/theorems/84c18e87-8161-48c1-a83c-afe697300581
-- title:
--   If $2(1-Cs)\,I(s)\le s\,I'(s)$ on $(0,S)$, then $e^{2Cs}I(s)/s^2$ is nondecreasing there
-- statement:
--   Let $C,S\in\mathbb{R}$ and let $I:\mathbb{R}\to\mathbb{R}$ have derivative $I'(s)$ at every $s\in(0,S)$, with
--   $$2(1-Cs)\,I(s)\ \le\ s\,I'(s)\qquad(0<s<S).$$
--   Then $s\mapsto e^{2Cs}\,I(s)/s^2$ is nondecreasing on $(0,S)$.
--
--   This is the form in which monotonicity of the energy ratio enters the monotonicity lemma for pseudoholomorphic curves.
--
--   **Formalization Note** The derivative is given as `HasDerivAt I (I' s) s` for `s ∈ Set.Ioo 0 S`; the conclusion is `MonotoneOn (fun s => Real.exp (2 * C * s) * I s / s ^ 2) (Set.Ioo 0 S)`. No sign of $I$ is assumed.
-- source:
--   Standard; used for the monotonicity lemma, A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace FiniteEnergyPlane

open Set

/-- Let `I` be differentiable on `(0, S)` with `2 (1 - C s) I(s) ≤ s I'(s)` there. Then
`s ↦ e^{2 C s} I(s) / s²` is nondecreasing on `(0, S)`. -/
theorem monotoneOn_exp_mul_div_sq {I I' : ℝ → ℝ} {C S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, 2 * (1 - C * s) * I s ≤ s * I' s) :
    MonotoneOn (fun s => Real.exp (2 * C * s) * I s / s ^ 2) (Ioo 0 S) := by
  sorry

end FiniteEnergyPlane
