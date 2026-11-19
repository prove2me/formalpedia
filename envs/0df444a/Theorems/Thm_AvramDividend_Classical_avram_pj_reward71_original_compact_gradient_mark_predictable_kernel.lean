-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
-- name    : AvramDividend.Classical.avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:52:52.651618+00:00
-- url     : https://prove2.me/theorems/be0c05d1-08d1-436f-8ca8-0b7cd9067a41
-- title:
--   Clipped C2 derivative finite-band signed physical jump kernel is predictable under strongly predictable prepayment reserve
-- statement:
--   Under a physical right-continuous predictable filtration, whenever the original prepayment left-limit Y is predictable and w is C2 on a compact open state band, the deterministically time-clipped, negative-finite-mark-band, discounted first-order kernel based on deriv w(Y) is predictable as a function of ((t,omega),z). This is a source-faithful analytic Borel composition lemma, with no stochastic mean or compensation hypotheses.
-- source:
--   Source-exact clipped predictable first-order jump kernel required for reward70 and reward60.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 × Ω → ℝ)
    (hY : Measurable[𝓕.rightCont.predictable] Y)
    (w : ℝ → ℝ) (Cband u v δ η : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hleft : 0 < u + δ) (huv : u + δ < v)
    (hv : v < Cband)
    (q : ℝ) (T : ℝ≥0) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        if p.1.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1.1 : ℝ))) *
          (if Y p.1 ∈ Icc (u + δ) v then
            deriv w (Y p.1) * p.2 else 0) else 0) := by sorry
