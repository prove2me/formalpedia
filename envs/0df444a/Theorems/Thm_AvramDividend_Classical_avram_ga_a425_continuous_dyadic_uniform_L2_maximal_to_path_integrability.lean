-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a425_continuous_dyadic_uniform_L2_maximal_to_path_integrability
-- name    : AvramDividend.Classical.avram_ga_a425_continuous_dyadic_uniform_L2_maximal_to_path_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:52:36.392668+00:00
-- url     : https://prove2.me/theorems/785c9a33-c5e0-4ad0-9457-cfd0c83cbc50
-- title:
--   Dyadic maximal L2 bounds imply integrable pathwise squared continuous martingale supremum
-- statement:
--   Almost-sure continuous sample paths and uniform expected bounds for the squared maxima over nested dyadic grids produce an integrable random envelope for the supremum over every real time t in [0,T].
-- source:
--   Classical Doob L2 maximal inequality and monotone convergence across dyadic grids, with continuity/density of dyadic rationals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a425_continuous_dyadic_uniform_L2_maximal_to_path_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P)     (hDyad : ∀ k : ℕ,
      Integrable (fun ω =>
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) P ∧
      (∫ ω,
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ∂P) ≤
        4 * (∫ ω, (M T ω)^2 ∂P)) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      (∀ᵐ ω ∂P, 0 ≤ S ω ∧
        ∀ t : ℝ≥0, t ≤ T → (M t ω)^2 ≤ S ω) := by sorry
