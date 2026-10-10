-- Prove2me | Theorems.Thm_FickDiffusion_erfc_solution_infinite_medium
-- name    : FickDiffusion.erfc_solution_infinite_medium
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:54.980069+00:00
-- url     : https://prove2.me/theorems/1500947a-e3c6-4dac-b674-6dcf8c617397
-- title:
--   Example solution 1 (infinite medium): n(x,t) = (n₀/2) erfc(x / (2√(Dt)))
-- statement:
--   Let $D>0$ and $n_0\in\mathbb R$, and set
--   $$n(x,t)=\frac{n_0}{2}\,\operatorname{erfc}\Big(\frac{x}{2\sqrt{Dt}}\Big).$$
--   Then:
--
--   1. $\dfrac{\partial n}{\partial t}(x,t)=D\,\dfrac{\partial^2 n}{\partial x^2}(x,t)$ for all $x\in\mathbb R$ and $t>0$;
--   2. for every $x>0$, $n(x,t)\to0$ as $t\to0^+$;
--   3. for every $x<0$, $n(x,t)\to n_0$ as $t\to0^+$.
--
--   So $n$ solves Fick's second law on the whole line with initial profile $n_0$ on $x<0$ and $0$ on $x>0$: a solution of concentration $n_0$ brought into contact with pure solvent.
--
--   **Formalization Note** The initial condition is expressed as pointwise limits as $t\to0^+$ away from the interface $x=0$ (at $x=0$ the value is $n_0/2$ for all $t>0$, consistent with any choice of $n(0,0)$).
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Example solution 1: constant concentration source and diffusion length" (p. 6), sentence beginning "If, in its turn, the diffusion space is infinite"

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem erfc_solution_infinite_medium (D n₀ : ℝ) (hD : 0 < D) :
    (∀ x t : ℝ, 0 < t →
      deriv (fun s => n₀ / 2 * erfc (x / (2 * Real.sqrt (D * s)))) t =
        D * deriv (fun y => deriv (fun z => n₀ / 2 * erfc (z / (2 * Real.sqrt (D * t)))) y) x) ∧
    (∀ x : ℝ, 0 < x →
      Tendsto (fun t => n₀ / 2 * erfc (x / (2 * Real.sqrt (D * t)))) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ x : ℝ, x < 0 →
      Tendsto (fun t => n₀ / 2 * erfc (x / (2 * Real.sqrt (D * t)))) (𝓝[>] 0) (𝓝 n₀)) := by sorry

end FickDiffusion
