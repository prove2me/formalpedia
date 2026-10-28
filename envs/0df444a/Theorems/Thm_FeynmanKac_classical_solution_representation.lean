-- Prove2me | Theorems.Thm_FeynmanKac_classical_solution_representation
-- name    : FeynmanKac.classical_solution_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:23:45.743997+00:00
-- url     : https://prove2.me/theorems/9ea9481c-a8f6-4fab-8b1d-e279234c56c7
-- title:
--   Feynman–Kac representation for a classical diffusion PDE solution
-- statement:
--   Let \(X^{t,x}\) be a non-explosive real Brownian SDE solution with time- and state-dependent drift \(\mu\) and diffusion coefficient \(\sigma\), started at \(X_t=x\) under probability law \(P^{t,x}\). Let \(V\ge0\) be a bounded measurable potential, \(f\) a bounded running source and \(\psi\) a bounded terminal payoff. Assume \(u\) is a bounded \(C^{1,2}\) classical solution of
--   $$
--   u_t+\mu u_x+\tfrac12\sigma^2u_{xx}-Vu+f=0,\qquad
--   u(x,T)=\psi(x)
--   $$
--   for \(t\le T\), with checkable square integrability of the discounted stochastic integrand \(D_{t,s}\sigma(X_s,s)u_x(X_s,s)\). The conclusion is
--   $$
--   u(x,t)=E^{t,x}\left[
--    e^{-\int_t^T V(X_s,s)\,ds}\psi(X_T)
--    +\int_t^T e^{-\int_t^r V(X_s,s)\,ds}f(X_r,r)\,dr
--   \right].
--   $$
--   The planned bounded-diffusion structure contains only independent SDE, adaptedness, measurability, boundedness and time-horizon data. Its PDE-solution predicate records derivatives and the displayed PDE, while square-integrability of the gradient is a separate checkable condition. Neither model nor predicate may assume this representation, an expectation identity, or the discounted-reward martingale. The current Lean declaration is a specification pending publication of those structures and remote elaboration, not a compiled theorem.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.classical_solution_representation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    u m.initialState m.initialTime =
      ∫ ω, (m.pathDiscount m.terminalTime ω *
          m.terminalPayoff (m.path m.terminalTime ω) +
        ∫ s in m.initialTime..m.terminalTime,
          m.pathDiscount s ω * m.runningSource (m.path s ω) s)
        ∂P := by sorry
