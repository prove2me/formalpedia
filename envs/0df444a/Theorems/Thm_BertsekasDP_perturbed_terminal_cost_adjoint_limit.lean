-- Prove2me | Theorems.Thm_BertsekasDP_perturbed_terminal_cost_adjoint_limit
-- name    : BertsekasDP.perturbed_terminal_cost_adjoint_limit
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T21:58:46.180655+00:00
-- url     : https://prove2.me/theorems/45a095fd-666b-4267-8fe1-cc43dc658f41
-- title:
--   Adjoint pairing computes the first variation of the terminal cost
-- statement:
--   Consider the fixed-horizon problem of `BertsekasCTModel` with $C^1$ data $f,g,h$, an admissible pair $(u,x)$ on $[0,T]$, and a costate $p$ that is continuous on $[0,T]$, satisfies the terminal condition $p(T)=\nabla h(x(T))$, and solves the adjoint equation
--
--   $$\dot p(t)=-\nabla_x H(x(t),u(t),p(t)),\qquad H(x,u,p)=g(x,u)+\langle p,f(x,u)\rangle,$$
--
--   off a finite set of times.
--
--   Fix $\tau\in(0,T)$ and let $\varepsilon\mapsto y_\varepsilon$ be a family of perturbed trajectories which, for all small $\varepsilon>0$, is continuous on $[\tau,T]$ and satisfies the *same* state equation $\dot y_\varepsilon=f(y_\varepsilon,u)$ with the *same* control $u$ off a finite set. Assume the initial deviation at $\tau$ has a first-order expansion,
--
--   $$\lim_{\varepsilon\downarrow 0}\frac{y_\varepsilon(\tau)-x(\tau)}{\varepsilon}=w.$$
--
--   Then the tail cost accumulated on $[\tau,T]$ has first variation given by the adjoint pairing at $\tau$:
--
--   $$\lim_{\varepsilon\downarrow 0}\frac1\varepsilon\left[\Big(h(y_\varepsilon(T))+\int_\tau^T g(y_\varepsilon(t),u(t))\,dt\Big)-\Big(h(x(T))+\int_\tau^T g(x(t),u(t))\,dt\Big)\right]=\langle p(\tau),w\rangle.$$
--
--   The mechanism is the classical pairing identity. Writing $\Delta_\varepsilon=y_\varepsilon-x$, the deviation obeys the variational equation up to a remainder that is $o(\lVert\Delta_\varepsilon\rVert)$ uniformly in $t$, because $f$ is $C^1$ and both trajectories remain in a compact tube; a Gronwall estimate gives $\lVert\Delta_\varepsilon\rVert=O(\varepsilon)$ on $[\tau,T]$. Differentiating $t\mapsto\langle p(t),\Delta_\varepsilon(t)\rangle$ off the finite exceptional set and using the adjoint equation shows that its increment cancels the first-order running-cost increment $\int_\tau^T\langle\nabla_x g(x,u),\Delta_\varepsilon\rangle$, while the terminal condition $p(T)=\nabla h(x(T))$ converts the terminal-cost increment into $\langle p(T),\Delta_\varepsilon(T)\rangle$. What survives is the pairing at the left endpoint, $\langle p(\tau),\Delta_\varepsilon(\tau)\rangle$, whose $\varepsilon$-quotient converges to $\langle p(\tau),w\rangle$.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Sections 4.2.3-4.2.4, equations (4.14)-(4.23), https://liberzon.csl.illinois.edu/teaching/cvoc/node68.html and https://liberzon.csl.illinois.edu/teaching/cvoc/node69.html; adjoint pairing identity (4.32), Section 4.2.8; terminal costs, Section 4.3.1.3, https://liberzon.csl.illinois.edu/teaching/cvoc/node82.html. Fixed-horizon Bolza specialization adapted to the finite-exception admissibility class of BertsekasCTModel (D. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Sections 3.2-3.3.1).

import Definitions.Def_BertsekasCTModel

open Filter
open scoped Topology

theorem BertsekasDP.perturbed_terminal_cost_adjoint_limit
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
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T)
    (y : ℝ → ℝ → EuclideanSpace ℝ (Fin n))
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (y ε) (Set.Icc τ M.T) ∧
        ∃ G : Finset ℝ, ∀ t ∈ Set.Icc τ M.T \ (G : Set ℝ),
          HasDerivAt (y ε) (M.f (y ε t) (u t)) t)
    (w : EuclideanSpace ℝ (Fin n))
    (hlim : Tendsto (fun ε => ε⁻¹ • (y ε τ - x τ)) (𝓝[>] (0 : ℝ)) (𝓝 w)) :
    Tendsto
      (fun ε => ε⁻¹ * ((M.h (y ε M.T) + ∫ t in τ..M.T, M.g (y ε t) (u t)) -
        (M.h (x M.T) + ∫ t in τ..M.T, M.g (x t) (u t))))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (p τ) w)) := by
  sorry
