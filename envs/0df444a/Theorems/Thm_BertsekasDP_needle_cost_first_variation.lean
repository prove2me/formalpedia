-- Prove2me | Theorems.Thm_BertsekasDP_needle_cost_first_variation
-- name    : BertsekasDP.needle_cost_first_variation
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T20:53:54.82074+00:00
-- url     : https://prove2.me/theorems/f11c1f86-5f73-4cdf-883e-03571d1016a2
-- title:
--   Cost first variation for a needle at a continuity time
-- statement:
--   Consider the fixed-horizon problem with continuously differentiable data $f,g,h$, cost
--
--   $$J(u,x)=h(x(T))+\int_0^T g(x(t),u(t))\,dt,$$
--
--   and Hamiltonian $H(x,u,p)=g(x,u)+\langle p,f(x,u)\rangle$. Let $(u,x)$ be an admissible pair starting at the prescribed initial state: $u$ takes values in the arbitrary constraint set $U$, has bounded image and is continuous off a finite set; $x$ is continuous and satisfies the state equation off a finite set. Suppose $p$ is continuous and satisfies the adjoint equation off a finite set, with terminal value $p(T)=\nabla h(x(T))$.
--
--   Fix a continuity time $\tau\in(0,T)$ of $u$ and any $v\in U$. Set
--
--   $$u_\varepsilon(s)=\begin{cases}v,&\tau-\varepsilon<s\le\tau,\\u(s),&\text{otherwise}.\end{cases}$$
--
--   There is a family of state trajectories $x_\varepsilon$ for which $(u_\varepsilon,x_\varepsilon)$ is admissible for every sufficiently small positive $\varepsilon$, and
--
--   $$\lim_{\varepsilon\downarrow0}\frac{J(u_\varepsilon,x_\varepsilon)-J(u,x)}{\varepsilon}
--   =H(x(\tau),v,p(\tau))-H(x(\tau),u(\tau),p(\tau)).$$
--
--   The assertion is a sensitivity formula for an arbitrary admissible pair; optimality is not assumed. No convexity or compactness of $U$, global Lipschitz bound on $f$, or one-sided control limits at exceptional times are required.
--
--   **Formalization Note** Admissibility of the perturbed family is an eventual statement as $\varepsilon$ tends to zero through positive values; values at other parameters are unrestricted.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Sections 4.2.3-4.2.4, equations (4.14)-(4.23), https://liberzon.csl.illinois.edu/teaching/cvoc/node68.html and https://liberzon.csl.illinois.edu/teaching/cvoc/node69.html; adjoint pairing identity (4.32), Section 4.2.8; terminal costs, Section 4.3.1.3, https://liberzon.csl.illinois.edu/teaching/cvoc/node82.html. Fixed-horizon Bolza specialization with the minimum-Hamiltonian sign convention and local C1 estimates on compact tubes; adapted to the finite-exception admissibility class of BertsekasCTModel.

import Definitions.Def_BertsekasCTModel

open Filter
open scoped Topology

theorem BertsekasDP.needle_cost_first_variation
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (hh : ContDiff ℝ 1 M.h)
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x p : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (hp : ContinuousOn p (Set.Icc 0 M.T))
    (hterm : p M.T = gradient M.h (x M.T))
    (F : Finset ℝ)
    (hadj : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt p
        (-gradient (fun y => BertsekasHamiltonian M y (u t) (p t)) (x t)) t)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) (huτ : ContinuousAt u τ)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ M.U) :
    ∃ xε : ℝ → ℝ → EuclideanSpace ℝ (Fin n),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        BertsekasCTAdmissibleFrom M 0 M.x0
          (fun s => if s ∈ Set.Ioc (τ - ε) τ then v else u s) (xε ε)) ∧
      Tendsto
        (fun ε =>
          (BertsekasCTCostFrom M 0
            (fun s => if s ∈ Set.Ioc (τ - ε) τ then v else u s) (xε ε) -
              BertsekasCTCostFrom M 0 u x) / ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (BertsekasHamiltonian M (x τ) v (p τ) -
          BertsekasHamiltonian M (x τ) (u τ) (p τ))) := by
  sorry
