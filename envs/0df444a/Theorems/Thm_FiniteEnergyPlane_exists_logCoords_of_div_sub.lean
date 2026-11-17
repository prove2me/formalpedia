-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_logCoords_of_div_sub
-- name    : FiniteEnergyPlane.exists_logCoords_of_div_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:51:51.476008+00:00
-- url     : https://prove2.me/theorems/145c350a-1021-4bc6-a776-dcd3a7ff00bd
-- title:
--   Cylindrical coordinates of a map asymptotic to a complex dilation
-- statement:
--   Let $\chi : \mathbb{C} \to \mathbb{C}$ and $\kappa \ne 0$, and suppose that $\chi(z)/z - \kappa$ decays like $e^{-bs}$ in $C^\infty$ ($b > 0$) in the cylindrical coordinates $z = e^{2\pi(s+it)}$ at $\infty$. Then there are $E : \mathbb{R}^2 \to \mathbb{R}^2$ decaying like $e^{-bs}$ in $C^\infty$ and $S \in \mathbb{R}$ such that for $s \ge S$ and all $t$
--   $$\chi\bigl(e^{2\pi(s+it)}\bigr) = e^{2\pi(s' + i t')},\qquad (s', t') = (s, t) + \Bigl(\tfrac{\log|\kappa|}{2\pi}, \tfrac{\arg \kappa}{2\pi}\Bigr) + E(s, t).$$
--
--   Role: writes a map asymptotic to $z \mapsto \kappa z$ at $\infty$ as an exponentially small perturbation of a translation of the cylinder.
--
--   Formalization Note: $e^{2\pi(s+it)}$ is `cylInf s t`; decay is `ExpDecayCInfty`.
-- source:
--   Standard calculus of exponential decay on cylindrical ends; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff Real

/-- Cylindrical coordinates of a map asymptotic to `z ↦ κ z`. If `χ(z)/z - κ` decays like `e^{-bs}`
in `C^∞` in the coordinates `z = e^{2π(s+it)}` (`κ ≠ 0`, `b > 0`), then far out
`χ(e^{2π(s+it)}) = e^{2π(s' + it')}` with `(s', t') = (s, t) + (log |κ|, arg κ)/(2π) + E(s, t)`,
where `E` decays like `e^{-bs}` in `C^∞`. -/
theorem exists_logCoords_of_div_sub (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ∃ (E : ℝ × ℝ → ℝ × ℝ) (S : ℝ), ExpDecayCInfty E b ∧ ∀ s ≥ S, ∀ t : ℝ,
      χ (cylInf s t) =
        cylInf ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).1
          ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).2 := by
  sorry

end FiniteEnergyPlane
