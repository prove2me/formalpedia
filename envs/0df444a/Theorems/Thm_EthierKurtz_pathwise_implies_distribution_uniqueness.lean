-- Prove2me | Theorems.Thm_EthierKurtz_pathwise_implies_distribution_uniqueness
-- name    : EthierKurtz.pathwise_implies_distribution_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:53:52.479061+00:00
-- url     : https://prove2.me/theorems/4a5dc92c-c13f-4f47-b9c8-d67cb95a9a6a
-- title:
--   Theorem 3.6 — pathwise uniqueness implies distribution uniqueness
-- statement:
--   For locally bounded Borel coefficients and any initial probability law, pathwise uniqueness for solutions driven by the same Brownian motion implies equality of the whole path laws of any two weak solutions.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 3, Theorem 3.6, printed p. 296 (PDF p. 305); solution conventions printed pp. 290–291 (PDF pp. 299–300).

import Definitions.Def_EthierKurtz_SDEPathwiseUnique

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

universe u

/-- Chapter 5 Theorem 3.6. Equality of whole path laws is expressed on the
coordinate sigma algebra. For continuous paths in Euclidean space this is
exactly equality of Borel laws on C([0,∞),ℝᵈ) with the compact-open topology.
No existence assumption, Lipschitz condition, or moment bound is imposed. -/
theorem pathwise_implies_distribution_uniqueness
    {d : ℕ}
    (σ : ℝ≥0 × SDEState d → SDEDiffusion d)
    (b : ℝ≥0 × SDEState d → SDEState d)
    (hσmeas : Measurable σ) (hbmeas : Measurable b)
    (hlocal : ∀ K : Set (ℝ≥0 × SDEState d), IsCompact K →
      ∃ C : ℝ, ∀ z ∈ K, ‖σ z‖ ≤ C ∧ ‖b z‖ ≤ C)
    (μ : Measure (SDEState d)) [IsProbabilityMeasure μ]
    (hunique : SDEPathwiseUnique.{u} σ b μ)
    {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (ℱ' : Filtration ℝ≥0 ‹MeasurableSpace Ω'›)
    (W X : ℝ≥0 → Ω → SDEState d) (W' X' : ℝ≥0 → Ω' → SDEState d)
    (hX : IsWeakSDESolution P ℱ σ b μ W X)
    (hX' : IsWeakSDESolution P' ℱ' σ b μ W' X') :
    Measure.map (fun ω t => X t ω) P = Measure.map (fun ω t => X' t ω) P' := by sorry
