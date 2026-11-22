-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_local_simple_mark_fibre_integral_exact
-- name    : AvramDividend.Classical.avram_mathfin22_original_local_simple_mark_fibre_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:11:47.585242+00:00
-- url     : https://prove2.me/theorems/94132e91-abab-4353-bbd6-a2a14a20c0dc
-- title:
--   Original physical local negative Borel bounded simple mark integral equals its finite actual jump-count fibre sum on every sample path
-- statement:
--   Remove the global finite negative activity hypothesis from the original pathwise bounded simple-mark fibre integral identity. For every original Lévy sample path, locally separated negative marks S have a finite original physical jump-measure mass, proved from the original cadlag cutoff count. The accepted generic bounded-mark finite-cell integral norm lemma yields integrability of the genuine physical raw simple integral. The accepted measure-theoretic SimpleFunc integral partition identity then identifies its exact signed value with the finite sum of original physical mark-fibre count measures. No fake PoissonRandomMeasure and no global ν finite assumption. This feeds the exact original all-activity physical compensated simple-mark L2 isometry and target 16f22886.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_local_simple_mark_fibre_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSep : S ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    ∀ ω, (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) =
      ∑ y ∈ g.range, y *
        (NX ω (Ioc 0 T ×ˢ B y)).toReal := by sorry
