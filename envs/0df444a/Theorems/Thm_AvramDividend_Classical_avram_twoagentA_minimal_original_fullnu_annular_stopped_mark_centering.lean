-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_minimal_original_fullnu_annular_stopped_mark_centering
-- name    : AvramDividend.Classical.avram_twoagentA_minimal_original_fullnu_annular_stopped_mark_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:26:10.170798+00:00
-- url     : https://prove2.me/theorems/7c40b768-73fd-4614-b346-da7d34bd1d46
-- title:
--   Original physical compensated annular gradient mark is stopped L1-centred without payoff integrability, cap or Gaussian restrictions
-- statement:
--   For any original spectrally negative Levy process and any adapted original dividend strategy, the original right-payment reserve left limit defines a predictable discounted gradient kernel on an interior compact state band and a finite negative-mark annulus. For every stopping time, its actual marked jump-count stochastic integral minus the original Levy compensator is L1 with zero expectation. No hypothesis about the stopped payoff, bound on the dividend cap, Lévy activity or Gaussian variance is required. This removes an actual integrability bottleneck inherited by the previously conditional source, and can be combined with the already Proved nonlinear marked Taylor source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_minimal_original_fullnu_annular_stopped_mark_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (Cband u v δ η : ℝ)
    (hleft : 0 < u + δ) (huv : u + δ < v)
    (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband) ) :
  (let T : ℝ≥0 := (n : ℝ≥0)
   let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
     (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
   let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
     ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
       Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
   let μT : Measure ℝ≥0 :=
     ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
   let H : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
     if p.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
       Real.exp (-(q * (p.1 : ℝ))) *
         (if Y (p.1, ω) ∈ Icc (u + δ) v then
           deriv w (Y (p.1, ω)) * p.2 else 0) else 0
   ∀ σ : Ω → ℝ≥0,
     IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)) →
     Integrable (fun ω =>
       (∫ p, (if p.1 ≤ σ ω then H ω p else 0) ∂(NX ω)) -
       (∫ t, ∫ z, (if t ≤ σ ω then H ω (t,z) else 0)
         ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) P ∧
     (∫ ω, ((∫ p, (if p.1 ≤ σ ω then H ω p else 0) ∂(NX ω)) -
       (∫ t, ∫ z, (if t ≤ σ ω then H ω (t,z) else 0)
         ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) ∂P) = 0) := by sorry
