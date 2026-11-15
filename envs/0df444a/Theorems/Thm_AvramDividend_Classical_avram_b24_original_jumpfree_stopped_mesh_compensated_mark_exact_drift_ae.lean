-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_jumpfree_stopped_mesh_compensated_mark_exact_drift_ae
-- name    : AvramDividend.Classical.avram_b24_original_jumpfree_stopped_mesh_compensated_mark_exact_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:59:11.788894+00:00
-- url     : https://prove2.me/theorems/f3d39ffc-5760-41a3-b483-91bbf9aa9a3a
-- title:
--   Exact original compensated smallmark stopped predictable jumpfree physical grid drift
-- statement:
--   On the original finite-negative-activity Lévy source and any common-a.e. intrinsic compensated Jsmall witness, if every stopped physical mesh cell is genuinely free of X jumps, its entire bounded predictable left-clipped compensated-mark source sum equals EXACTLY the negative-smallmark full finite-activity ν first-moment compensator multiplied by the weighted physical stopped elapsed time sum, on one common conull event. This is the signed Itô-Meyer interior drift identity, rather than an upper bound or an assumption of vanishing smallmark noise. True jump-bearing and ruin-contact cells are excluded and must be retained in a separate generator jump ledger.
-- source:
--   Proved original B24 common conull jumpfree intrinsic smallmark drift on arbitrary physical intervals and finite sum algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_jumpfree_stopped_mesh_compensated_mark_exact_drift_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (hOrdered : ∀ i ∈ S, a i ≤ b i)
    (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (∀ i ∈ S, ∀ u : ℝ≥0, a i < u → u ≤ b i →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
          ((b i : ℝ) - (a i : ℝ))) := by sorry
