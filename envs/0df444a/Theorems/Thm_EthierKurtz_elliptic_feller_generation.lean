-- Prove2me | Theorems.Thm_EthierKurtz_elliptic_feller_generation
-- name    : EthierKurtz.elliptic_feller_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:03:53.947794+00:00
-- url     : https://prove2.me/theorems/ae1e5a11-b25d-4e45-b629-89131255ed1e
-- title:
--   Theorem 1.6 — uniformly elliptic Feller generation
-- statement:
--   Bounded Hölder covariance and drift with symmetric globally uniformly elliptic covariance generate a positive strongly continuous contraction semigroup on C₀; the generator is exactly the closure of the smooth compactly supported diffusion graph, and the semigroup is conservative in the bounded-pointwise sense.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, Theorem 1.6, printed p. 370 (PDF p. 379); operator (1.15), printed p. 368 (PDF p. 377).

import Definitions.Def_EthierKurtz_diffusionOperator
import Definitions.Def_EthierKurtz_diffusionGraph
import Definitions.Def_EthierKurtz_boundedPointwiseClosure

open Filter
open scoped Topology ZeroAtInfty ContDiff

namespace EthierKurtz

/-- Uniformly elliptic Hölder diffusions generate Feller semigroups, with
exactly the closure of the smooth compactly supported graph as generator.
The Chapter 1 semigroup/generator clauses are expanded unchanged, since no
compiled local import artifact exists for that completed capstone. -/
theorem elliptic_feller_generation (d : ℕ) [NeZero d]
    (a : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ K : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) (hK : 0 < K)
    (hsym : ∀ x u v, inner ℝ (a x u) v = inner ℝ u (a x v))
    (hbounded : ∃ M : ℝ, ∀ x, ‖a x‖ + ‖b x‖ ≤ M)
    (hholder : ∀ x y, ‖a x - a y‖ + ‖b x - b y‖ ≤ K * ‖x - y‖ ^ μ)
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x θ,
      ‖θ‖ = 1 → ε ≤ inner ℝ θ (a x θ)) :
    let A := closure (diffusionGraph a b)
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    ∃ T : ℝ → C₀(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ]
        C₀(EuclideanSpace ℝ (Fin d), ℝ),
      T 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
      (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
      (∀ f, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) ∧
      (fun _ => (1, 0)) ∈ boundedPointwiseClosure
        ((fun fg : C₀(EuclideanSpace ℝ (Fin d), ℝ) ×
          C₀(EuclideanSpace ℝ (Fin d), ℝ) => fun x => (fg.1 x, fg.2 x)) '' A) := by sorry
