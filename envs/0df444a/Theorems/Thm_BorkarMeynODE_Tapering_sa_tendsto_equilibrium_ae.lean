-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_sa_tendsto_equilibrium_ae
-- name    : BorkarMeynODE.Tapering.sa_tendsto_equilibrium_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:46:07.573094+00:00
-- url     : https://prove2.me/theorems/5fa19e6c-7cf1-42a6-ac98-c36fe4e3e79d
-- title:
--   Theorem 2.2 — under (A1), (A2), (TS) and global asymptotic stability of $x^*$, $X(n)\to x^*$ almost surely
-- statement:
--   Let $(\Omega,\mathcal F,\mathsf P)$ be a probability space, and let $X(n),M(n)$ in $\mathbb R^d$ follow the stochastic approximation recursion
--   $$
--   X(n+1) = X(n) + a(n)\big[h(X(n)) + M(n+1)\big], \qquad n\ge0, \tag{1.1}
--   $$
--   where $h$ and $h_\infty$ satisfy (A1), the noise satisfies (A2) with some constant $C_0<\infty$ for the natural filtration of $X$, and the deterministic step sizes satisfy (TS). Suppose the ODE
--   $$
--   \dot x(t) = h(x(t)) \tag{1.2}
--   $$
--   has a unique globally asymptotically stable equilibrium $x^*$. Then for every initial condition $X(0)=x_0\in\mathbb R^d$,
--   $$
--   X(n) \to x^* \qquad \text{almost surely as } n\to\infty .
--   $$
--
--   Together with Theorem 2.1 (i) this is the O.D.E. method without an a priori stability assumption: the convergence of the recursion follows from properties of two deterministic ODEs, (1.2) and its fluid limit (1.5).
--
--   **Formalization Note** Uniqueness of the equilibrium is stated as the hypothesis that $h(y)=0$ implies $y=x^*$; it already follows from global asymptotic stability. The theorem is stated for every probability space and every noise sequence satisfying (A2); the initial condition is deterministic.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 450, Theorem 2.2

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
import Definitions.Def_BorkarMeynODE_Tapering_Stepsizes
import Definitions.Def_BorkarMeynODE_Tapering_SAModel

namespace BorkarMeynODE.Tapering

open MeasureTheory Filter Topology

/-- **Theorem 2.2** (Borkar–Meyn 2000, p. 450). Assume (A1) for `(h, h_∞)`, (A2) with
constant `C₀` for the natural filtration of `X`, and tapering step sizes (TS), and let `xs` be
the unique equilibrium of the ODE (1.2) `ẋ = h(x)`, globally asymptotically stable. Then for
every deterministic initial condition `X(0) = x₀ ∈ ℝ^d`, `X(n) → xs` almost surely.
Uniqueness is stated as the hypothesis `huniq`; it is implied by global asymptotic stability
(a constant solution at another equilibrium would not converge to `xs`). -/
theorem sa_tendsto_equilibrium_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ) (C₀ : ℝ)
    (hA1 : AssumptionA1 h hInf) (hTS : TaperingStepsize a)
    (xs : EuclideanSpace ℝ (Fin d)) (hGAS : IsGloballyAsymptoticallyStable h xs)
    (huniq : ∀ y, h y = 0 → y = xs)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n))
    (hrec : IsSARecursion h a X M) (hA2 : AssumptionA2 P X M hX C₀)
    (x₀ : EuclideanSpace ℝ (Fin d)) (h0 : ∀ ω, X 0 ω = x₀) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 xs) := by sorry

end BorkarMeynODE.Tapering
