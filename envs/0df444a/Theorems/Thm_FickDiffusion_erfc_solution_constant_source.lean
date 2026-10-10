-- Prove2me | Theorems.Thm_FickDiffusion_erfc_solution_constant_source
-- name    : FickDiffusion.erfc_solution_constant_source
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:23.391781+00:00
-- url     : https://prove2.me/theorems/2a5483fa-aa08-4cde-aeb2-149b2543e2cb
-- title:
--   Example solution 1: constant concentration source, n(x,t) = n₀ erfc(x / (2√(Dt)))
-- statement:
--   Let $D>0$ and $n_0\in\mathbb R$, and set
--   $$n(x,t)=n_0\,\operatorname{erfc}\Big(\frac{x}{2\sqrt{Dt}}\Big),\qquad \operatorname{erfc}(u)=\frac{2}{\sqrt\pi}\int_u^\infty e^{-s^2}ds .$$
--   Then:
--
--   1. $n$ satisfies Fick's second law: $\dfrac{\partial n}{\partial t}(x,t)=D\,\dfrac{\partial^2 n}{\partial x^2}(x,t)$ for all $x\in\mathbb R$ and $t>0$;
--   2. the boundary concentration is maintained: $n(0,t)=n_0$ for all $t>0$;
--   3. the medium is initially free of solute: for every $x>0$, $n(x,t)\to0$ as $t\to0^+$.
--
--   This is the classical solution for diffusion into a semi-infinite medium from a surface held at constant concentration $n_0$.
--
--   **Formalization Note** Derivatives use Mathlib's `deriv`. Clause 2 is written with the literal argument $0/(2\sqrt{Dt})$, i.e. $\operatorname{erfc}(0)$.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Example solution 1: constant concentration source and diffusion length" (p. 6), first displayed equation and the surrounding paragraph

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem erfc_solution_constant_source (D n₀ : ℝ) (hD : 0 < D) :
    (∀ x t : ℝ, 0 < t →
      deriv (fun s => n₀ * erfc (x / (2 * Real.sqrt (D * s)))) t =
        D * deriv (fun y => deriv (fun z => n₀ * erfc (z / (2 * Real.sqrt (D * t)))) y) x) ∧
    (∀ t : ℝ, 0 < t → n₀ * erfc (0 / (2 * Real.sqrt (D * t))) = n₀) ∧
    (∀ x : ℝ, 0 < x →
      Tendsto (fun t => n₀ * erfc (x / (2 * Real.sqrt (D * t)))) (𝓝[>] 0) (𝓝 0)) := by sorry

end FickDiffusion
