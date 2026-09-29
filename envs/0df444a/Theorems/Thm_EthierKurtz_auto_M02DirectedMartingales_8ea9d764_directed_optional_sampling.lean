-- Prove2me | Theorems.Thm_EthierKurtz_auto_M02DirectedMartingales_8ea9d764_directed_optional_sampling
-- name    : EthierKurtz.auto_M02DirectedMartingales_8ea9d764_directed_optional_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T18:47:20.790527+00:00
-- url     : https://prove2.me/theorems/b2e6587d-9ce2-477d-854f-d7f2b0a70b8d
-- title:
--   Theorem 8.7 — Optional sampling on metric lattices
-- statement:
--   Let I be a metric lattice whose intervals are separable from above, and let X be a real right-continuous martingale. For measurable lattice-valued stopping times τ₁ ≤ τ₂, assume sequences uₙ,vₙ satisfy P(uₙ ≤ τ₁ ≤ τ₂ ≤ vₙ) → 1 and E[|X(vₙ)| 1_{¬(τ₂ ≤ vₙ)}] → 0, and assume X(τ₂) is integrable. Then E[X(τ₂) | F_{τ₁}] = X(τ₁) almost surely.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 2 §8, Theorem 8.7, printed pp. 87–88 (PDF pp. 96–97); conventions and (8.6) on printed p. 85 (PDF p. 94).

import Definitions.Def_auto_M02DirectedMartingales_8ea9d764_SeparableFromAbove
import Definitions.Def_auto_M02DirectedMartingales_8ea9d764_directedStoppedSigma

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EthierKurtz

theorem auto_M02DirectedMartingales_8ea9d764_directed_optional_sampling
    {I Ω : Type*} [Lattice I] [MetricSpace I]
    [MeasurableSpace I] [BorelSpace I] [mΩ : MeasurableSpace Ω]
    (hInf : Continuous (fun p : I × I => p.1 ⊓ p.2))
    (hSup : Continuous (fun p : I × I => p.1 ⊔ p.2))
    (hIntervals : ∀ u v : I, u ≤ v → SeparableFromAbove (Set.Icc u v))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration I mΩ) (X : I → Ω → ℝ)
    (hMart : Martingale X ℱ μ)
    (hIntegrable : ∀ u : I, Integrable (X u) μ)
    (hRight : ∀ u : I, ∀ ω : Ω,
      Tendsto (fun v : I => X (u ⊔ v) ω) (𝓝 u) (𝓝 (X u ω)))
    (τ₁ τ₂ : Ω → I) (hMeas₁ : Measurable τ₁) (hMeas₂ : Measurable τ₂)
    (hStop₁ : IsStoppingTime ℱ (fun ω => (τ₁ ω : WithTop I)))
    (hStop₂ : IsStoppingTime ℱ (fun ω => (τ₂ ω : WithTop I)))
    (hOrder : ∀ ω, τ₁ ω ≤ τ₂ ω)
    (u v : ℕ → I)
    (hExhaust : Tendsto
      (fun n => μ {ω | u n ≤ τ₁ ω ∧ τ₁ ω ≤ τ₂ ω ∧ τ₂ ω ≤ v n})
      atTop (𝓝 1))
    (hTail : Tendsto
      (fun n => ∫⁻ ω in {ω | ¬ τ₂ ω ≤ v n}, ENNReal.ofReal |X (v n) ω| ∂μ)
      atTop (𝓝 0))
    (hStoppedIntegrable : Integrable (fun ω => X (τ₂ ω) ω) μ) :
    μ[(fun ω => X (τ₂ ω) ω) | directedStoppedSigma ℱ τ₁] =ᵐ[μ]
      (fun ω => X (τ₁ ω) ω) := by sorry

end EthierKurtz
