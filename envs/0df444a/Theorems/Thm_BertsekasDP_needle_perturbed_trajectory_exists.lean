-- Prove2me | Theorems.Thm_BertsekasDP_needle_perturbed_trajectory_exists
-- name    : BertsekasDP.needle_perturbed_trajectory_exists
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T21:58:57.33744+00:00
-- url     : https://prove2.me/theorems/bf57024f-f577-4046-acff-669d21cf8001
-- title:
--   Existence and first-order expansion of the needle-perturbed trajectory
-- statement:
--   Consider the fixed-horizon control system $\dot x = f(x,u)$ of `BertsekasCTModel` with continuously differentiable dynamics $f$, and let $(u,x)$ be an admissible pair on $[0,T]$ starting from $x(0)=x_0$: the control takes values in $U$, has bounded image and is continuous off a finite set, and the state is continuous and solves the state equation off a finite set.
--
--   Fix an interior time $\tau\in(0,T)$ at which $u$ is continuous, and a value $v\in U$. For $\varepsilon>0$ let
--
--   $$u_\varepsilon(s)=\begin{cases} v, & s\in(\tau-\varepsilon,\tau],\\ u(s), & \text{otherwise,}\end{cases}$$
--
--   be the needle (spike) variation of $u$ of width $\varepsilon$ ending at $\tau$.
--
--   The assertion is that the perturbed control admits an admissible trajectory for all sufficiently small $\varepsilon>0$, together with the two quantitative properties that the needle construction is meant to supply. There exist a family $\varepsilon\mapsto x_\varepsilon$ of state trajectories and a constant $K$ such that, for all small $\varepsilon>0$:
--
--   1. the pair $(u_\varepsilon,x_\varepsilon)$ is admissible on $[0,T]$ with $x_\varepsilon(0)=x_0$;
--   2. the perturbation is causal: $x_\varepsilon(s)=x(s)$ for every $s\in[0,\tau-\varepsilon]$;
--   3. the trajectory stays within $O(\varepsilon)$ of the base state on the needle window: $\lVert x_\varepsilon(s)-x(\tau)\rVert\le K\varepsilon$ for every $s\in[\tau-\varepsilon,\tau]$;
--
--   and moreover the state deviation created by the needle has the first-order expansion
--
--   $$\lim_{\varepsilon\downarrow 0}\frac{x_\varepsilon(\tau)-x(\tau)}{\varepsilon}=f(x(\tau),v)-f(x(\tau),u(\tau)).$$
--
--   No global Lipschitz hypothesis is imposed: $f$ is only assumed $C^1$, so solutions must be produced on a compact tube around the base trajectory. Continuity of $u$ at $\tau$ is what makes the limit equal to the value $f(x(\tau),u(\tau))$ at the single time $\tau$.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Sections 4.2.3-4.2.4, equations (4.14)-(4.23), https://liberzon.csl.illinois.edu/teaching/cvoc/node68.html and https://liberzon.csl.illinois.edu/teaching/cvoc/node69.html; adjoint pairing identity (4.32), Section 4.2.8; terminal costs, Section 4.3.1.3, https://liberzon.csl.illinois.edu/teaching/cvoc/node82.html. Fixed-horizon Bolza specialization adapted to the finite-exception admissibility class of BertsekasCTModel (D. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Sections 3.2-3.3.1).

import Definitions.Def_BertsekasCTModel

open Filter
open scoped Topology

theorem BertsekasDP.needle_perturbed_trajectory_exists
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) (huτ : ContinuousAt u τ)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ M.U) :
    ∃ (xε : ℝ → ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        BertsekasCTAdmissibleFrom M 0 M.x0
            (fun s => if s ∈ Set.Ioc (τ - ε) τ then v else u s) (xε ε) ∧
          (∀ s ∈ Set.Icc 0 (τ - ε), xε ε s = x s) ∧
          (∀ s ∈ Set.Icc (τ - ε) τ, ‖xε ε s - x τ‖ ≤ K * ε)) ∧
      Tendsto (fun ε => ε⁻¹ • (xε ε τ - x τ)) (𝓝[>] (0 : ℝ))
        (𝓝 (M.f (x τ) v - M.f (x τ) (u τ))) := by
  sorry
