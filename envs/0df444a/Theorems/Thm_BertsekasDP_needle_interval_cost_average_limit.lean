-- Prove2me | Theorems.Thm_BertsekasDP_needle_interval_cost_average_limit
-- name    : BertsekasDP.needle_interval_cost_average_limit
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T21:58:48.365519+00:00
-- url     : https://prove2.me/theorems/aa56a57c-512c-454f-8dfa-335648629a57
-- title:
--   Running-cost average over the needle window
-- statement:
--   Let $g$ be a continuous running cost, $(u,x)$ an admissible pair on $[0,T]$, $\tau\in(0,T)$ a continuity time of $u$, and $v$ a control value. Let $\varepsilon\mapsto y_\varepsilon$ be any family of state functions which, for all small $\varepsilon>0$, is continuous on the window $[\tau-\varepsilon,\tau]$ and stays within $O(\varepsilon)$ of $x(\tau)$ there:
--
--   $$\lVert y_\varepsilon(s)-x(\tau)\rVert\le K\varepsilon\qquad (s\in[\tau-\varepsilon,\tau]).$$
--
--   Then the running cost over the shrinking window has the average
--
--   $$\lim_{\varepsilon\downarrow 0}\frac1\varepsilon\left(\int_{\tau-\varepsilon}^{\tau} g(y_\varepsilon(s),v)\,ds-\int_{\tau-\varepsilon}^{\tau} g(x(s),u(s))\,ds\right)=g(x(\tau),v)-g(x(\tau),u(\tau)).$$
--
--   Both terms are handled by the same mean-value principle: the integrand of the first integral converges uniformly on the window to the constant $g(x(\tau),v)$ because $y_\varepsilon\to x(\tau)$ uniformly there and $g$ is continuous; the integrand of the second converges uniformly to $g(x(\tau),u(\tau))$ because $x$ is continuous at $\tau$ and $u$ is continuous at $\tau$. This is the contribution of the needle interval itself to the first variation of the cost.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Sections 4.2.3-4.2.4, equations (4.14)-(4.23), https://liberzon.csl.illinois.edu/teaching/cvoc/node68.html and https://liberzon.csl.illinois.edu/teaching/cvoc/node69.html; adjoint pairing identity (4.32), Section 4.2.8; terminal costs, Section 4.3.1.3, https://liberzon.csl.illinois.edu/teaching/cvoc/node82.html. Fixed-horizon Bolza specialization adapted to the finite-exception admissibility class of BertsekasCTModel (D. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Sections 3.2-3.3.1).

import Definitions.Def_BertsekasCTModel

open Filter
open scoped Topology

theorem BertsekasDP.needle_interval_cost_average_limit
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hg : Continuous (Function.uncurry M.g))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) (huτ : ContinuousAt u τ)
    (v : EuclideanSpace ℝ (Fin m))
    (y : ℝ → ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (y ε) (Set.Icc (τ - ε) τ) ∧
        ∀ s ∈ Set.Icc (τ - ε) τ, ‖y ε s - x τ‖ ≤ K * ε) :
    Tendsto
      (fun ε => ε⁻¹ * ((∫ s in (τ - ε)..τ, M.g (y ε s) v) -
        ∫ s in (τ - ε)..τ, M.g (x s) (u s)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (M.g (x τ) v - M.g (x τ) (u τ))) := by
  sorry
