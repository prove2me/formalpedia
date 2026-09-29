-- Prove2me | Theorems.Thm_BertsekasDP_minimized_hamiltonian_extension
-- name    : BertsekasDP.minimized_hamiltonian_extension
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T20:54:05.302238+00:00
-- url     : https://prove2.me/theorems/a703c444-349c-4b9e-873c-60bbe5ca169d
-- title:
--   Continuous extension and zero derivative of the minimized autonomous Hamiltonian
-- statement:
--   Let $T>0$ and let $f,g$ be continuously differentiable autonomous data, with
--
--   $$H(x,u,p)=g(x,u)+\langle p,f(x,u)\rangle.$$
--
--   Let $u:[0,T]\to U\subseteq\mathbb R^m$ have bounded image, and let $x,p:[0,T]\to\mathbb R^n$ be continuous. Suppose that for a finite set $F$, the control is continuous on $[0,T]\setminus F$, and on that same set the state and adjoint equations and Hamiltonian minimization hold:
--
--   $$\dot x(t)=f(x(t),u(t)),\qquad \dot p(t)=-\nabla_xH(x(t),u(t),p(t)),$$
--
--   $$H(x(t),u(t),p(t))\le H(x(t),v,p(t))\qquad(v\in U).$$
--
--   Then there exists $E:[0,T]\to\mathbb R$ such that
--
--   $$E\text{ is continuous on }[0,T],\qquad E(t)=H(x(t),u(t),p(t))\quad(t\in[0,T]\setminus F),$$
--
--   $$E'(t)=0\quad(t\in(0,T)\setminus F).$$
--
--   This is the analytic extension and envelope step in autonomous Hamiltonian conservation. It requires neither optimality of the trajectory, terminal conditions, nor regularity of a value function. The control set need not be closed, compact, or convex.
--
--   **Formalization Note** The Hamiltonian's values at exceptional times need not equal the continuous extension. Boundedness of the actual control image is assumed, while one-sided limits at exceptional times are not. This formulation handles the precise control class in BertsekasCTModel.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Section 4.2.9.2, equation (4.36) and the envelope argument following it, https://liberzon.csl.illinois.edu/teaching/cvoc/node76.html. Minimum-sign version of the autonomous envelope argument. The continuous-extension formulation adapts that argument to bounded controls continuous off a finite set without assuming one-sided control limits; it does not assert the free-final-time zero Hamiltonian conclusion.

import Definitions.Def_BertsekasCTModel

theorem BertsekasDP.minimized_hamiltonian_extension
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x p : ℝ → EuclideanSpace ℝ (Fin n))
    (F : Finset ℝ)
    (huU : ∀ t ∈ Set.Icc 0 M.T, u t ∈ M.U)
    (hub : Bornology.IsBounded (u '' Set.Icc 0 M.T))
    (hu : ContinuousOn u (Set.Icc 0 M.T \ (F : Set ℝ)))
    (hx : ContinuousOn x (Set.Icc 0 M.T))
    (hp : ContinuousOn p (Set.Icc 0 M.T))
    (hstate : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt x (M.f (x t) (u t)) t)
    (hadj : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt p
        (-gradient (fun y => BertsekasHamiltonian M y (u t) (p t)) (x t)) t)
    (hmin : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      IsMinOn (fun v => BertsekasHamiltonian M (x t) v (p t)) M.U (u t)) :
    ∃ E : ℝ → ℝ,
      ContinuousOn E (Set.Icc 0 M.T) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        E t = BertsekasHamiltonian M (x t) (u t) (p t)) ∧
      (∀ t ∈ Set.Ioo 0 M.T \ (F : Set ℝ), HasDerivAt E 0 t) := by
  sorry
