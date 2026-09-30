-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_sa_bounded_ae
-- name    : BorkarMeynODE.Tapering.sa_bounded_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:45:35.08257+00:00
-- url     : https://prove2.me/theorems/19be5c72-bbec-4c9b-b6b2-46780af95c9d
-- title:
--   Theorem 2.1 (i) — under (TS) the stochastic approximation iterates are almost surely bounded
-- statement:
--   Let $(\Omega,\mathcal F,\mathsf P)$ be a probability space, and let $X(n),M(n)$ in $\mathbb R^d$ follow the stochastic approximation recursion
--   $$
--   X(n+1) = X(n) + a(n)\big[h(X(n)) + M(n+1)\big], \qquad n\ge0, \tag{1.1}
--   $$
--   where $h$ and $h_\infty$ satisfy (A1), the noise satisfies (A2) with some constant $C_0<\infty$ for the natural filtration of $X$, and the deterministic step sizes satisfy (TS): $0<a(n)\le1$, $\sum_n a(n)=\infty$, $\sum_n a(n)^2<\infty$. Then for every initial condition $X(0)=x_0\in\mathbb R^d$,
--   $$
--   \sup_n \|X(n)\| < \infty \qquad \text{almost surely.}
--   $$
--
--   This is the paper's stability theorem: asymptotic stability of the origin (assumed in (A1); Lemma 4.1 upgrades it to global exponential stability) for the fluid-limit ODE $\dot x=h_\infty(x)$ implies almost sure boundedness of the iterates, the hypothesis that classical ODE-method convergence proofs have to assume.
--
--   **Formalization Note** The theorem is stated for every probability space and every pair of processes satisfying (1.1) and (A2); the initial condition is deterministic. "$\sup_n\|X(n)\|<\infty$" is written as boundedness above of $\{\|X(n)\|:n\ge0\}$, avoiding the real-valued supremum of an unbounded set.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 450, Theorem 2.1 (i)

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
import Definitions.Def_BorkarMeynODE_Tapering_Stepsizes
import Definitions.Def_BorkarMeynODE_Tapering_SAModel

namespace BorkarMeynODE.Tapering

open MeasureTheory

/-- **Theorem 2.1 (i)** (Borkar–Meyn 2000, p. 450). Assume (A1) for `(h, h_∞)`, (A2) with
constant `C₀` for the natural filtration of `X`, and tapering step sizes (TS). Then for every
deterministic initial condition `X(0) = x₀ ∈ ℝ^d` the iterates of (1.1) are almost surely
bounded: `sup_n ‖X(n)‖ < ∞` a.s. The statement holds for every probability space and every
noise sequence `M` satisfying (A2). -/
theorem sa_bounded_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ) (C₀ : ℝ)
    (hA1 : AssumptionA1 h hInf) (hTS : TaperingStepsize a)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n))
    (hrec : IsSARecursion h a X M) (hA2 : AssumptionA2 P X M hX C₀)
    (x₀ : EuclideanSpace ℝ (Fin d)) (h0 : ∀ ω, X 0 ω = x₀) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun n => ‖X n ω‖) := by sorry

end BorkarMeynODE.Tapering
