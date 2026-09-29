-- Prove2me | Theorems.Thm_EthierKurtz_jump_feller_generation
-- name    : EthierKurtz.jump_feller_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:28:31.102573+00:00
-- url     : https://prove2.me/theorems/41cbab3e-741d-4fd6-92ca-6ab767113d57
-- title:
--   Theorem 3.1 — weighted jump-kernel Feller generation
-- statement:
--   For a weakly continuous probability transition kernel and a nonnegative continuous rate satisfying the source’s weighted vanishing, compact-mass, and signed integral bounds, the weighted jump graph closes to the generator of a positive conservative strongly continuous contraction semigroup, and compactly supported continuous functions form a core.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, Theorem 3.1, printed pp. 376–377 (PDF pp. 385–386), equations (3.1)–(3.5).

import Definitions.Def_EthierKurtz_weightedJumpGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open MeasureTheory Filter
open scoped Topology ZeroAtInfty

namespace EthierKurtz

/-- Weighted jump generators on a locally compact noncompact space have a
conservative Feller closure and a compactly supported continuous core.
The positive-rate integrability clause prevents the total Bochner integral
from interpreting a divergent positive η moment as zero. -/
theorem jump_feller_generation
    (E : Type*) [MetricSpace E] [LocallyCompactSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (hnoncompact : ¬ IsCompact (Set.univ : Set E))
    (rate γ η : C(E, ℝ)) (μ : E → ProbabilityMeasure E)
    (hrate : ∀ x, 0 ≤ rate x)
    (htransition : ∀ B : Set E, MeasurableSet B →
      Measurable (fun x => (μ x : Measure E) B))
    (hweak : Continuous μ)
    (hγ : ∀ x, 0 < γ x) (hη : ∀ x, 0 < η x)
    (hγvanish : Tendsto (fun x => (γ x)⁻¹) (cocompact E) (𝓝 0))
    (hηvanish : Tendsto (fun x => (η x)⁻¹) (cocompact E) (𝓝 0))
    (h32 : ∃ C₁ : ℝ, ∀ x, rate x / γ x ≤ C₁)
    (h33 : ∀ K : Set E, IsCompact K →
      Tendsto (fun x => rate x * ((μ x : Measure E) K).toReal)
        (cocompact E) (𝓝 0))
    (h34 : ∃ C₂ : ℝ, ∀ x,
      rate x * (∫ y, (γ x - γ y) / γ y ∂(μ x : Measure E)) ≤ C₂)
    (h35integrable : ∀ x, 0 < rate x →
      Integrable (fun y => (η y - η x) / η x) (μ x : Measure E))
    (h35 : ∃ C₃ : ℝ, ∀ x,
      rate x * (∫ y, (η y - η x) / η x ∂(μ x : Measure E)) ≤ C₃) :
    let graph := weightedJumpGraph rate γ μ
    let A := closure graph
    let bpClosure := fun (H : Set (E → ℝ × ℝ)) =>
      {f | ∀ S : Set (E → ℝ × ℝ), H ⊆ S →
        (∀ (u : ℕ → E → ℝ × ℝ) (v : E → ℝ × ℝ),
          (∀ n, u n ∈ S) → (∃ M : ℝ, ∀ n x, ‖u n x‖ ≤ M) →
          (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) → v ∈ S) → f ∈ S}
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    (∃ T : ℝ → C₀(E, ℝ) →L[ℝ] C₀(E, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) ∧
      (fun _ => (1, 0)) ∈ bpClosure
        ((fun fg : C₀(E, ℝ) × C₀(E, ℝ) => fun x => (fg.1 x, fg.2 x)) '' A)) ∧
    (∀ f : C₀(E, ℝ), HasCompactSupport (f : E → ℝ) →
      ∃ g, (f, g) ∈ graph) ∧
    closure {fg : C₀(E, ℝ) × C₀(E, ℝ) |
      fg ∈ graph ∧ HasCompactSupport (fg.1 : E → ℝ)} = A := by sorry
