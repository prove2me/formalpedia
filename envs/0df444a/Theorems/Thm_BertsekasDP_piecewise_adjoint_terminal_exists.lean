-- Prove2me | Theorems.Thm_BertsekasDP_piecewise_adjoint_terminal_exists
-- name    : BertsekasDP.piecewise_adjoint_terminal_exists
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T20:53:42.501145+00:00
-- url     : https://prove2.me/theorems/97ed50ed-f437-4ada-a4f2-257be30a5aa2
-- title:
--   Terminal-value adjoint equation along a bounded piecewise continuous control
-- statement:
--   Let $T>0$, let $f:\mathbb R^n\times\mathbb R^m\to\mathbb R^n$ and $g:\mathbb R^n\times\mathbb R^m\to\mathbb R$ be continuously differentiable, and put
--
--   $$H(x,u,p)=g(x,u)+\langle p,f(x,u)\rangle.$$
--
--   Let $x:[0,T]\to\mathbb R^n$ be continuous and let $u:[0,T]\to\mathbb R^m$ have bounded image and be continuous away from a finite set. For every prescribed terminal vector $q\in\mathbb R^n$, there exist a continuous function $p:[0,T]\to\mathbb R^n$ and a finite set $F$ such that
--
--   $$p(T)=q,\qquad \dot p(t)=-\nabla_x H(x(t),u(t),p(t))\quad(t\in[0,T]\setminus F).$$
--
--   This is the linear terminal-value adjoint equation underlying first-variation formulas. Neither optimality nor the state equation is assumed, and the terminal vector is arbitrary.
--
--   **Formalization Note** The functions are defined on the whole real line. Endpoints may be included in $F$, so the two-sided derivative notation imposes no endpoint extension condition. Boundedness and continuity away from finitely many times are the exact hypotheses; one-sided limits of $u$ at those times are not assumed.
-- source:
--   D. Liberzon, Calculus of Variations and Optimal Control Theory, Section 4.2.8, equation (4.31), https://liberzon.csl.illinois.edu/teaching/cvoc/node73.html. Linear adjoint terminal-value existence specialized to cost multiplier +1 and arbitrary terminal vector. The bounded finite-exception control formulation is an adaptation to Definitions.Def_BertsekasCTModel.

import Definitions.Def_BertsekasCTModel

theorem BertsekasDP.piecewise_adjoint_terminal_exists
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hu : BertsekasPiecewiseContinuousOn u (Set.Icc 0 M.T))
    (hx : ContinuousOn x (Set.Icc 0 M.T))
    (q : EuclideanSpace ℝ (Fin n)) :
    ∃ (p : ℝ → EuclideanSpace ℝ (Fin n)) (F : Finset ℝ),
      ContinuousOn p (Set.Icc 0 M.T) ∧ p M.T = q ∧
      ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        HasDerivAt p
          (-gradient (fun y => BertsekasHamiltonian M y (u t) (p t)) (x t)) t := by
  sorry
