-- Prove2me | Theorems.Thm_EthierKurtz_spin_flip_feller_generation
-- name    : EthierKurtz.spin_flip_feller_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:42:45.089638+00:00
-- url     : https://prove2.me/theorems/4e92c25b-693f-4549-a57c-992d57a508ca
-- title:
--   Theorem 3.5 — spin-flip Feller generation and cylinder core
-- statement:
--   For a countable spin set with nonnegative continuous flip rates that are uniformly bounded and have uniformly summable coordinate influences, the full summable-variation spin-flip graph has a continuous image on its stated domain, its closure is single-valued and is exactly the generator of a positive conservative strongly continuous contraction semigroup, and finite-coordinate continuous functions form a core.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, Theorem 3.5, equations (3.24)–(3.25), printed p. 381 (PDF p. 390); Feller convention on printed p. 166 and core convention on printed p. 17.

import Definitions.Def_EthierKurtz_spinFlipGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- The full spin-flip generation theorem, including the cylinder-function
core. No finite total rate or finite number of sites is imposed. -/
theorem spin_flip_feller_generation (S : Type*) [Countable S]
    (c : S → C(S → Bool, ℝ))
    (hnonneg : ∀ i η, 0 ≤ c i η)
    (hrates : ∃ M : ℝ, ∀ i, ‖c i‖ ≤ M)
    (hinfluence : ∃ M : ℝ, ∀ i,
      Summable (spinVariation (c i)) ∧ (∑' j, spinVariation (c i) j) ≤ M) :
    let graph := spinFlipGraph c
    let A := closure graph
    (∀ f : C(S → Bool, ℝ), Summable (spinVariation f) →
      ∃ g, (f, g) ∈ graph) ∧
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    (∃ T : ℝ → C(S → Bool, ℝ) →L[ℝ] C(S → Bool, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ η, 0 ≤ f η) → ∀ η, 0 ≤ T t f η) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A)) ∧
    closure {fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) |
      fg ∈ graph ∧ ∃ F : Finset S, ∀ η ξ : S → Bool,
        (∀ i ∈ F, η i = ξ i) → fg.1 η = fg.1 ξ} = A := by sorry
