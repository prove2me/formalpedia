-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
-- name    : AvramDividend.Classical.avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:29:51.009398+00:00
-- url     : https://prove2.me/theorems/039486e9-bd51-4a05-93ad-a0f0544140a6
-- title:
--   Finite-horizon bounded jointly measurable physical-grid common L2 limit forces two-mesh nested energy Cauchy
-- statement:
--   For a probability or finite sample measure, an arbitrary positive finite physical-time interval and jointly measurable grid coefficients bounded only inside that interval, convergence of integrated expected squared difference to a common stopped limit implies two-parameter Cauchy convergence of integrated expected squared mesh-pair differences on that same interval.
-- source:
--   Direct bridge Gaussian original selected-band B216 to two-mesh energy using B218 and B157's proven measurable zero extension on a finite interval.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (n : ℕ) (hn : 0 < n)
    (K : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hKm : ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2))
    (hHm : Measurable (fun z : ℝ × Ω => H z.1 z.2))
    (BK BH : ℝ) (hBK : 0 ≤ BK) (hBH : 0 ≤ BH)
    (hKb : ∀ m t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) →
      |K m t ω| ≤ BK)
    (hHb : ∀ t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) →
      |H t ω| ≤ BH)
    (hlim : Tendsto (fun m : ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω - H t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by sorry
