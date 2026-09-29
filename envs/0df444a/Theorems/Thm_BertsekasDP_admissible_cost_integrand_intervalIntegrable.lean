-- Prove2me | Theorems.Thm_BertsekasDP_admissible_cost_integrand_intervalIntegrable
-- name    : BertsekasDP.admissible_cost_integrand_intervalIntegrable
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T21:58:48.654717+00:00
-- url     : https://prove2.me/theorems/d88aecca-029a-4bd8-9587-cfc42e59622e
-- title:
--   Interval integrability of the running cost along an admissible pair
-- statement:
--   Let $g$ be a continuous running cost on state-control pairs and let $(u,x)$ be admissible on $[t_0,T]$ from the state $\xi$ in the sense of `BertsekasCTAdmissibleFrom`: $u$ has bounded image on $[t_0,T]$ and is continuous off a finite set, and $x$ is continuous on $[t_0,T]$.
--
--   Then for any two times $a,b\in[t_0,T]$ the running cost is interval integrable:
--
--   $$t\mapsto g(x(t),u(t))\quad\text{is integrable on } [a\wedge b, a\vee b].$$
--
--   The integrand is continuous off a finite set, hence almost everywhere continuous and measurable, and it is bounded because $x([t_0,T])$ is compact, $u([t_0,T])$ is bounded, and $g$ is continuous on the resulting compact product. This is the fact that makes the cost functional $h(x(T))+\int_{t_0}^{T} g(x(t),u(t))\,dt$ of an admissible pair a genuine Lebesgue integral, and it is what allows the cost to be split at intermediate times.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Sections 4.2.3-4.2.4, equations (4.14)-(4.23), https://liberzon.csl.illinois.edu/teaching/cvoc/node68.html and https://liberzon.csl.illinois.edu/teaching/cvoc/node69.html; adjoint pairing identity (4.32), Section 4.2.8; terminal costs, Section 4.3.1.3, https://liberzon.csl.illinois.edu/teaching/cvoc/node82.html. Fixed-horizon Bolza specialization adapted to the finite-exception admissibility class of BertsekasCTModel (D. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Sections 3.2-3.3.1).

import Definitions.Def_BertsekasCTModel

open Filter
open scoped Topology

theorem BertsekasDP.admissible_cost_integrand_intervalIntegrable
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hg : Continuous (Function.uncurry M.g))
    (t₀ : ℝ) (ξ : EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M t₀ ξ u x)
    (a b : ℝ) (ha : a ∈ Set.Icc t₀ M.T) (hb : b ∈ Set.Icc t₀ M.T) :
    IntervalIntegrable (fun t => M.g (x t) (u t)) MeasureTheory.volume a b := by
  sorry
