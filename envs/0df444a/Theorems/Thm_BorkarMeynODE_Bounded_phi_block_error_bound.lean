-- Prove2me | Theorems.Thm_BorkarMeynODE_Bounded_phi_block_error_bound
-- name    : BorkarMeynODE.Bounded.phi_block_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:48:07.257878+00:00
-- url     : https://prove2.me/theorems/9e465025-d8a5-4f72-aedb-e3bf210022ac
-- title:
--   Lemma 4.7 — conditional mean-square error of the scaled ODE approximation is $O(\bar\alpha)$
-- statement:
--   Assume (A1) for $h$ and $h_\infty$, and let $C_0$ be the constant of (A2). Fix a block length $T > 0$. Then there is a constant $C_2 < \infty$ with the following property. Let the stepsizes satisfy (BS) with bounds $\underline\alpha < \bar\alpha$, let $X$ follow the recursion (1.1) with noise $M$ satisfying (A2) with constant $C_0$, started from a deterministic $X(0) = x_0 \in \mathbb{R}^d$, and let $\hat\phi_j$ be the solution of the scaled ODE (4.1) $\dot x = h_{r(j)}(x)$ on block $j$ started from $\phi_j(T(j))$. Then for every block $j \ge 0$ and every $t \in [T(j), T(j+1)]$, almost surely,
--
--   $$\mathsf E\big[\|\phi_j(t) - \hat\phi_j(t)\|^2 \mid \mathcal F_{m(j)}\big] \le C_2\, \bar\alpha, \qquad \mathsf E\big[\|\phi_j(t)\|^2 \mid \mathcal F_{m(j)}\big] \le C_2,$$
--
--   and both squared norms are integrable. Here $\phi_j$ is the interpolation of $X(n)/r(j)$ with $r(j) = \max(1, \|X(m(j))\|)$, and $\mathcal F_n$ is the natural filtration of the iterates.
--
--   The constant $C_2$ depends only on $h$, $h_\infty$, $C_0$ and $T$. It is uniform over the stepsizes (in particular over $\bar\alpha$), the process and $X(0)$. This uniformity is what makes the choice $\alpha^* = \eta/(2C_2)$ in the proof of Theorem 2.1(ii) meaningful.
--
--   **Formalization Note** The page conditions on $\mathcal F_{n(j)}$; $n(j)$ is never defined and the proof conditions on $\mathcal F_{m(j)}$, which is what is stated. The page also quantifies $j$ twice ("for all $j \ge 0$, $\sup_{j \ge 0, \dots}$"); the statement holds for every $j$ and every $t$ in the closed block. Integrability is part of the conclusion, so nothing is assumed about the objects compared.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 464, Lemma 4.7

import Mathlib
import Definitions.Def_BorkarMeynODE_Bounded_ODEStability
import Definitions.Def_BorkarMeynODE_Bounded_SAModel
import Definitions.Def_BorkarMeynODE_Bounded_TimeGrid

namespace BorkarMeynODE.Bounded

open MeasureTheory Filter Topology

/-- Lemma 4.7 (Borkar–Meyn 2000, p. 464). Under (A1), (A2) and (BS), for a fixed block length
`T > 0` there is a constant `C₂ < ∞` such that for every block `j` and every
`t ∈ [T(j), T(j+1)]`,
(i) `E[‖φ_j(t) − φ̂_j(t)‖² | 𝓕_{m(j)}] ≤ C₂ ᾱ` and (ii) `E[‖φ_j(t)‖² | 𝓕_{m(j)}] ≤ C₂`
almost surely (and both squared norms are integrable).
`C₂` depends on `h`, `h_∞`, `C₀` and `T` only, not on the stepsizes (in particular not on `ᾱ`),
the process, or `X(0)`. The page's `𝓕_{n(j)}` is a typo for `𝓕_{m(j)}`. -/
theorem phi_block_error_bound {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) (C₀ : ℝ) (T : ℝ) (hT : 0 < T) :
    ∃ C₂ : ℝ,
      ∀ (αlo αhi : ℝ) (a : ℕ → ℝ), BoundedStepsize αlo αhi a →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n)),
        (∀ n, StronglyMeasurable (M n)) → IsSARecursion h a X M →
        AssumptionA2 P X M hX C₀ →
        ∀ x₀ : EuclideanSpace ℝ (Fin d), (∀ ω, X 0 ω = x₀) →
        ∀ φh : ℕ → Ω → ℝ → EuclideanSpace ℝ (Fin d),
          (∀ (j : ℕ) (ω : Ω), IsPhiHatBlock h a T X j ω (φh j ω)) →
        ∀ j : ℕ, ∀ t ∈ Set.Icc (blockTime a T j) (blockTime a T (j + 1)),
          (Integrable (fun ω => ‖phiBlock a T X j ω t - φh j ω t‖ ^ 2) P ∧
            P[fun ω => ‖phiBlock a T X j ω t - φh j ω t‖ ^ 2 |
                Filtration.natural (β := fun _ => EuclideanSpace ℝ (Fin d)) X hX
                  (blockIndex a T j)]
              ≤ᵐ[P] fun _ => C₂ * αhi) ∧
          (Integrable (fun ω => ‖phiBlock a T X j ω t‖ ^ 2) P ∧
            P[fun ω => ‖phiBlock a T X j ω t‖ ^ 2 |
                Filtration.natural (β := fun _ => EuclideanSpace ℝ (Fin d)) X hX
                  (blockIndex a T j)]
              ≤ᵐ[P] fun _ => C₂) := by sorry

end BorkarMeynODE.Bounded
