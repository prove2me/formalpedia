-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_law_from_fine_original_grids
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_law_from_fine_original_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:41:42.233447+00:00
-- url     : https://prove2.me/theorems/63f4aa92-41c6-45ac-9e21-929b65c7796c
-- title:
--   Genuine original BV Lévy N_X total negative jump count has Poisson law via source-path fine-grid convergence
-- statement:
--   For the actual source X on the original sample space, in BV finite-negative-activity regime, let a deterministic sequence of n-cell strictly increasing grids partition [0,T] (n>0), with mesh→0, equal cell widths and the correct original-X grid Bernoulli rare-event scaling n(1−e^(−h_nν((−∞,0))))→r. Then the probability, under the original P, that its **literal intrinsic original-path jump counting measure** N_X((0,T]×ℝ) equals k is exactly the Poisson(r) mass exp(−r)r^k/k!. In contrast to previous Proved grid-only scaling limits, the random event is the actual jump measure of X, not a constructed auxiliary Lévy process. The hypotheses are explicit realizable deterministic mesh conditions; the unconditioned canonical time-horizon intensity r=Tν((−∞,0)) still needs a uniform-grid rate lemma.
-- source:
--   Combine canonically Proved X-grid active-count Poisson scaling limit 8be1f776-b9c8-4639-880a-1f1fbf7db762 with genuine original source N_X fine-grid eventual count equality cc7abaca-d041-4ec1-ae5f-0c8d8f5772aa (proof pending at authoring time), and original-X finite-grid measurability 7d565b48-2aee-434c-8f46-b4db7429c950 (repair pending). Construct measurable liminf original-grid event E, identify E=ᵐ[P]{N_X=k} via eventual equal count, use MeasureTheory.measure_congr despite possible noncompletion of original P, apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure and ENNReal.tendsto_toReal, then uniqueness of real limits. No constructed model or Brownian/jump Lévy–Itô representation assumed; predictable mark compensation remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_law_from_fine_original_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (ht : ∀ n : ℕ, Monotone (grid n))
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (h : ℕ → ℝ)
    (hgap : ∀ n i : ℕ, i < n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)) = h n)
    (r : ℝ)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - Real.exp (-(h n * (X.ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 r))
    (k : ℕ) :
    P.real {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal)} =
      Real.exp (-r) * r ^ k / (k.factorial : ℝ) := by sorry
