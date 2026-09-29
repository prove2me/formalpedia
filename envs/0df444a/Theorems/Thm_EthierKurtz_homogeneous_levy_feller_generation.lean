-- Prove2me | Theorems.Thm_EthierKurtz_homogeneous_levy_feller_generation
-- name    : EthierKurtz.homogeneous_levy_feller_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:29:15.214837+00:00
-- url     : https://prove2.me/theorems/0717f218-ebba-46c2-9122-4bfc32ed5d40
-- title:
--   Theorem 3.4 — homogeneous Lévy Feller generation
-- statement:
--   A constant-coefficient compensated Lévy operator with symmetric nonnegative covariance and finite weighted jump measure closes to the generator of a positive conservative strongly continuous contraction semigroup; its full C-hat-two graph and smooth compactly supported core have the stated closures.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, Theorem 3.4 and equation (3.22), printed p. 380 (PDF p. 389).

import Definitions.Def_EthierKurtz_homogeneousLevyGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_boundedPointwiseClosure

open MeasureTheory Filter
open scoped Topology ZeroAtInfty ContDiff

namespace EthierKurtz

/-- Homogeneous Lévy operators, including degenerate covariance, generate
conservative Feller semigroups with the full Ĉ² graph closure and C_c^∞ core. -/
theorem homogeneous_levy_feller_generation (d : ℕ) [NeZero d]
    (a : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d)) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hsym : ∀ u v, inner ℝ (a u) v = inner ℝ u (a v))
    (hnonneg : ∀ u, 0 ≤ inner ℝ u (a u))
    (hfinite : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      ‖y‖ ^ 2 / (1 + ‖y‖ ^ 2)) μ) :
    let graph := homogeneousLevyGraph a b μ
    let A := closure graph
    (∀ f : C₀(EuclideanSpace ℝ (Fin d), ℝ),
      IsCTwiceVanishing (f : EuclideanSpace ℝ (Fin d) → ℝ) →
      ∃ g, (f, g) ∈ graph) ∧
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    (∃ T : ℝ → C₀(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ]
        C₀(EuclideanSpace ℝ (Fin d), ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) ∧
      (fun _ => (1, 0)) ∈ boundedPointwiseClosure
        ((fun fg : C₀(EuclideanSpace ℝ (Fin d), ℝ) ×
          C₀(EuclideanSpace ℝ (Fin d), ℝ) => fun x => (fg.1 x, fg.2 x)) '' A)) ∧
    closure {fg : C₀(EuclideanSpace ℝ (Fin d), ℝ) ×
        C₀(EuclideanSpace ℝ (Fin d), ℝ) |
      fg ∈ graph ∧ ContDiff ℝ ∞ (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ) ∧
        HasCompactSupport (fg.1 : EuclideanSpace ℝ (Fin d) → ℝ)} = A := by sorry
