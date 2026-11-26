-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_retimed_weighted_process_limits
-- name    : BellWilliams2001.ThresholdPolicy.retimed_weighted_process_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:06:37.599468+00:00
-- url     : https://prove2.me/theorems/b8ddaad0-3683-5956-ab4d-0451efa3d09b
-- title:
--   Process limits for retimed and weighted primitive paths
-- statement:
--   A compact stochastic time change close to a deterministic Lipschitz clock preserves finite limits and the asymptotic modulus after linear projection with convergent coefficients and drift.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem retimed_weighted_process_limits {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hF : ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η)
    (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ) (α : Fin k → ℝ) (β : ℝ)
    (ha : Tendsto a atTop (𝓝 α)) (hb : Tendsto b atTop (𝓝 β))
    (G : ℕ → Ω → ℝ → Fin k → ℝ) (g : ℝ → Fin k → ℝ)
    (hG : UocInProb P G g)
    (hg : ∀ t : ℝ, 0 ≤ t → ∀ i, g t i ∈ Icc 0 t)
    (hgLip : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ i, |g s i-g t i| ≤ |s-t|)
    (hGt : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t → ∀ i, G n ω t i ∈ Icc 0 t)
    (Y : ℕ → Ω → ℝ → Fin 1 → ℝ)
    (hY : ∀ n t, 0 ≤ t → AEMeasurable (fun ω => Y n ω t) P)
    (hYeq : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t →
      Y n ω t = ![(∑ i, a n i * X n ω (G n ω t i) i) + b n*t]) :
    let W (ω : Ω') (t : ℝ) := ![(∑ i, α i * Z ω (g t i) i) + β*t]
    (∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Y n ω s-Y n ω t‖} ≤ ENNReal.ofReal η) := by sorry

end BellWilliams2001.ThresholdPolicy
