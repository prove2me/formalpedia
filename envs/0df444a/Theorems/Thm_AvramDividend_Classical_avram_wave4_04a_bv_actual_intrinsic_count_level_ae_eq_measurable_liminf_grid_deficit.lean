-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:38:04.207973+00:00
-- url     : https://prove2.me/theorems/6a97b834-8508-4fac-b370-7b6925caf252
-- title:
--   Literal original BV Lévy N_X count-level event equals a measurable liminf of true source drift-grid count events almost surely
-- statement:
--   For the original bounded-variation finite-activity Lévy process X and any sequence of increasingly fine strict finite partitions of [0,T], each fixed integer k has a measurable original-sample-space liminf proxy formed from actual X drift-deficient grid count events. Almost surely under original P, this proxy coincides with the literal original-path N_X((0,T]×ℝ)=k event. No completion of the original filtration or measurability of the arbitrary exceptional-path N_X count event is assumed. The theorem provides the rigorous probability-transfer interface from proved binomial/Poisson source-grid laws to literal source N_X.
-- source:
--   Apply canonically Proved short-mesh pathwise intrinsic N_X equals source grid drift-deficit count (separately authored after original jump-path bridge). For each ω on its full source event, the sample-dependent positive mesh gap and deterministic mesh→0 ensure eventual identity of the literal count and finite measurable grid count. Use Filter.mem_liminf_iff_eventually_mem to identify level-k events, together with accepted original-adaptedness-based Measurable grid count 7d565b48-2aee-434c-8f46-b4db7429c950 and pinned MeasurableSet.measurableSet_liminf. The result leaves actual compensator, marked-band law and UBV representation open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (k : ℕ) :
    MeasurableSet (Filter.liminf
      (fun n : ℕ => {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k})
      atTop) ∧
      (∀ᵐ ω ∂P,
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) = (k : ENNReal) ↔
          ω ∈ (Filter.liminf
      (fun n : ℕ => {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k})
      atTop)) := by sorry
