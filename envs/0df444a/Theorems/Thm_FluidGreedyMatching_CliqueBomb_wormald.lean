-- Prove2me | Theorems.Thm_FluidGreedyMatching_CliqueBomb_wormald
-- name    : FluidGreedyMatching.CliqueBomb.wormald
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:23.232707+00:00
-- url     : https://prove2.me/theorems/e29d471d-3dc7-4d7d-8e8b-bddf94f28b56
-- title:
--   Theorem 2.1 — Wormald differential-equation approximation
-- statement:
--   Let $Z_{n,t}\in\mathbb R^a$ be arbitrary real adapted processes on probability spaces which may vary with size $n\ge1$. Assume $\|Z_{n,t}\|_\infty\le C_0n$ and $Z_{n,0}=nz_0$. Let $D\subset\mathbb R\times\mathbb R^a$ be bounded, connected and open with $(0,z_0)\in D$. Let $f$ be Lipschitz on the nonnegative-time part of $D$. Suppose that before first exit from $D$, jumps have norm at most a fixed $\beta>0$ and the conditional drift differs from $f(t/n,Z_{n,t}/n)$ by at most $\lambda_*(n)\to0$.
--
--   There is a unique ODE trajectory $z'=f(\tau,z)$ from $z_0$ on its maximal nonnegative interval in $D$, extending arbitrarily close to the boundary. For every positive $\lambda(n)\to0$ with $\lambda(n)>\lambda_*(n)$ eventually, and every sufficiently large fixed $C$, there are positive constants $A,B$, independent of $n,t$ and the sample path, such that for all sufficiently large $n$,
--   $$P_n\!\left(\exists t\le n\tau_{C\lambda(n)}:\ \|Z_{n,t}-nz(t/n)\|_\infty>A\lambda(n)n\right)
--   \le B\frac\beta{\lambda(n)}\exp\!\left(-\frac{n\lambda(n)^3}{\beta^3}\right).$$
--   Here $\tau_{C\lambda(n)}$ is the supremum of times through which the entire ODE path has maximum-norm distance at least $C\lambda(n)$ from $\partial D$. This retains the full tracking theorem rather than only a power-scale corollary.
--
--   **Formalization Note** Bounds are almost sure at each step. The adapted finite-dimensional real coordinates and their bounded increments are integrable; conditional expectations therefore have their usual meaning.
--
--   Differences from the source:
--   - encoding: positive integer sizes n tending to infinity → sequence index j with size j+1; reason: this bijectively retains every positive size and its asymptotic limit
--   - encoding: real adapted processes, a named unique solution, exit time and boundary clearance → changing probability spaces, finite maximum-norm products, an explicit maximal solution with overlap uniqueness, and a supremum with zero inserted; reason: these express the same probability and ODE objects, including the irrelevant small-size empty-clearance case
--   - encoding: bounded jumps beta and asymptotic O terms with lambda greater than lambda-star → beta is positive and O terms have positive constants uniform in size, time and path, with eventual strict scale inequality; reason: positivity gives the printed fractions their domain; finite exceptions do not affect asymptotic claims
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Theorem 2.1, p. 7

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_ProcessModel

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology NNReal

namespace FluidGreedyMatching.CliqueBomb

/-- Theorem 2.1, p. 7: arbitrary finite-dimensional real adapted processes,
uniform tracking with the printed exponential failure scale. -/
theorem wormald {a : ℕ} (P : ProcessFamily a)
    (z₀ : Vec a) (C₀ β : ℝ) (hβ : 0 < β)
    (D : Set (ℝ × Vec a)) (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D)
    (hDconn : IsConnected D) (hDinit : (0, z₀) ∈ D)
    (f : ℝ × Vec a → Vec a)
    (hf : ∃ L : ℝ≥0, LipschitzOnWith L f {p ∈ D | 0 ≤ p.1})
    (lamStar : ℕ → ℝ) (hstar : Tendsto lamStar atTop (𝓝 0))
    (hbounded : ∀ n t, ∀ᵐ ω ∂P.law n, ‖P.Z n t ω‖ ≤ C₀ * scale n)
    (hinit : ∀ n, ∀ᵐ ω ∂P.law n, P.Z n 0 ω = scale n • z₀)
    (hjumps : ∀ n t, ∀ᵐ ω ∂P.law n, beforeExit P D n t ω →
      ‖increment P n t ω‖ ≤ β)
    (hdrift : ∀ n t, ∀ᵐ ω ∂P.law n, beforeExit P D n t ω →
      ‖meanIncrement P n t ω - f ((t : ℝ) / scale n, normalized P n t ω)‖ ≤ lamStar n) :
    ∃ (S : ℝ) (z : ℝ → Vec a), maximalDomainSolution D f z₀ S z ∧
      ∀ lam : ℕ → ℝ, Tendsto lam atTop (𝓝 0) → (∀ n, 0 < lam n) →
        (∀ᶠ n in atTop, lamStar n < lam n) →
        ∃ Cmin : ℝ, 0 < Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
          ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ n in atTop,
            ((P.law n) {ω | ∃ t : ℕ,
              (t : ℝ) ≤ cutoffTime D S z C (lam n) * scale n ∧
              A * lam n * scale n < ‖P.Z n t ω - scale n • z ((t : ℝ) / scale n)‖}).toReal ≤
              B * (β / lam n) * Real.exp (-(scale n) * (lam n)^3 / β^3) := by sorry

end FluidGreedyMatching.CliqueBomb
