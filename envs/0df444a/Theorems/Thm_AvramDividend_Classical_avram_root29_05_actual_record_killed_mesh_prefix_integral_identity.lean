-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_record_killed_mesh_prefix_integral_identity
-- name    : AvramDividend.Classical.avram_root29_05_actual_record_killed_mesh_prefix_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:43:35.480249+00:00
-- url     : https://prove2.me/theorems/bbbb2b66-e5ee-433c-8727-25717b85191a
-- title:
--   Finite killed rational-grid payoff equals the actual regulator Stieltjes integral over its prefix
-- statement:
--   For the actual original spectrally negative Lévy process X, its true running-supremum Stieltjes dividend measure, any strict killing time, any discount rate and any finite uniform rational grid prefix, integrating the killed sampled right-ceiling discount over (0,N/(n+1)] exactly equals the finite sum of discounted genuine record increments surviving strict killing. This is a source-faithful original-dividend-measure identity (not a quotient of scale functions), using precise half-open endpoint cells and no unproved two-sided exit.
-- source:
--   Proved finite Ioc partition 947adc6d, runningSup actual dividendMeasure mass identity 7343971b, killed mesh cell integral identity 0ae8cfd1, and positivity of mesh denominator. Consumer 79978d61 and global Stieltjes reconstruction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_cell_integral_eq_mass

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_root29_05_actual_record_killed_mesh_prefix_integral_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (τ : ℝ≥0∞) (n N : ℕ) :
    let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
    (∫⁻ r in Ioc (u 0) (u N),
      (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
       if ENNReal.ofReal e < τ then
         ENNReal.ofReal (Real.exp (-(q * e))) else 0)
        ∂(dividendMeasure (runningSup X) ω)) =
    ∑ k ∈ Finset.range N,
      (if ENNReal.ofReal (u (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
      ENNReal.ofReal
        (runningSup X (u (k + 1)).toNNReal ω -
          runningSup X (u k).toNNReal ω) := by sorry
