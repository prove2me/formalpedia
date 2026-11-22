-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
-- name    : AvramDividend.Classical.avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:20:55.95481+00:00
-- url     : https://prove2.me/theorems/764dc9ab-c026-4473-9eb7-40ed4814e37b
-- title:
--   Original physical mark bounded simple-function quantization converges pointwise at any bounded random time
-- statement:
--   New source-faithful pathwise original physical Lévy jump mark quantisation at ANY sample-path-dependent finite clock ρ bounded by deterministic T, without requiring the clock to be a stopping time. The fixed-T true original separated negative-band NX point count is finite for every path, so the restricted physical jump measure at ρ is finite and its mass cannot exceed that at T. Original bounded finite-cell integral norm bound gives uniform absolute control by the full-T raw jump count, and the already Proved bounded simple-mark integral dominated convergence source applies for each ω at T=(ρ ω). The marked physical integrals of f_k converge to the true measurable mark g at the same random clock. This is the missing random-clock pathwise transfer for proving stopped true z-weighted negative-band signed jump integral centring via optional stopping of finite simple approximants, no global finite activity or synthetic Poisson measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integrals_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hfBound : ∀ k z, z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))) →
      |f k z| ≤ 1)
    (hfLimit : ∀ z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))),
      Tendsto (fun k => f k z) atTop (𝓝 (g z)))
    (ρ : Ω → ℝ≥0) (hρ : ∀ ω, ρ ω ≤ T) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∫ p in Ioc 0 (ρ ω) ×ˢ B, f k p.2 ∂NX ω
    let J : Ω → ℝ := fun ω =>
      ∫ p in Ioc 0 (ρ ω) ×ˢ B, g p.2 ∂NX ω
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    (∀ ω k, |F k ω| ≤ N ω) ∧
    (∀ ω, Tendsto (fun k => F k ω) atTop (𝓝 (J ω))) := by sorry
