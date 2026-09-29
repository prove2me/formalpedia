-- Prove2me | Theorems.Thm_EthierKurtz_exclusion_feller_generation
-- name    : EthierKurtz.exclusion_feller_generation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T06:59:59.558977+00:00
-- url     : https://prove2.me/theorems/304a0fdf-0018-4922-897a-32eedbc6f2af
-- title:
--   Theorem 3.6 — exclusion-process Feller generation and cylinder core
-- statement:
--   For a countable site set with nonnegative symmetric continuous exchange rates, symmetric nonnegative dominating weights with uniformly bounded summable rows, and uniformly gamma-controlled single-site influences, the full weighted two-site-variation exclusion graph has a continuous image on its stated domain, its closure is single-valued and is exactly the generator of a positive conservative strongly continuous contraction semigroup, and finite-coordinate continuous functions form a core.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, Theorem 3.6, equations (3.26)–(3.29), printed p. 381 (PDF p. 390); Feller convention on printed p. 166 and core convention on printed p. 17.

import Definitions.Def_EthierKurtz_exclusionGraph
import Definitions.Def_EthierKurtz_spinVariation
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Exclusion-process generation, full weighted domain, and cylinder core.
The influence bound uses single-site flips, not particle exchanges. -/
theorem exclusion_feller_generation (S : Type*) [Countable S]
    (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η)
    (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdiag : ∀ i, c i i = 0)
    (hc_symm : ∀ i j, c i j = c j i)
    (hdom : ∀ i j η, c i j η ≤ γ i j)
    (hγ_symm : ∀ i j, γ i j = γ j i)
    (hrows : ∃ M : ℝ, ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
    (hinfluence : ∃ K : ℝ, ∀ i j,
      Summable (spinVariation (c i j)) ∧
        (∑' k, spinVariation (c i j) k) ≤ K * γ i j) :
    let graph := exclusionGraph c γ
    let A := closure graph
    (∀ f : C(S → Bool, ℝ),
      Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation f ij.1 ij.2) →
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
