-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_fullnu_finite_annular_stopped_martingale_L1_centered
-- name    : AvramDividend.Classical.avram_twoagentA_original_fullnu_finite_annular_stopped_martingale_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:24:44.932931+00:00
-- url     : https://prove2.me/theorems/506d5f09-36e9-43b8-a952-e149ee1bf72d
-- title:
--   Finite families of original same-space compensated negative annular gradient marks are jointly stopped integrable and mean zero
-- statement:
--   For the actual spectrally negative Levy process and the same bounded stopping time, any finite family of original jump-measure compensated, discounted, compactly localised gradient marks from negative Levy annuli has an integrable mean-zero sum. The thresholds may vary by mark family member; arbitrary Levy activity and Gaussian variance are allowed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_minimal_original_fullnu_annular_stopped_mark_centering
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_fullnu_finite_annular_stopped_martingale_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (Cband u v δ : ℝ)
    (hleft : 0 < u + δ) (huv : u + δ < v) (hv : v < Cband)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (S : Finset ℕ) (η : ℕ → ℝ)
    (hη : ∀ i, 0 < η i ∧ η i < 1)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let T : ℝ≥0 := (n : ℝ≥0)
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let K : ℕ → Ω → (ℝ≥0 × ℝ) → ℝ := fun i ω p =>
      if p.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-(η i)) then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if Y (p.1, ω) ∈ Icc (u + δ) v then
            deriv w (Y (p.1, ω)) * p.2 else 0) else 0
    let L : ℕ → Ω → ℝ := fun i ω =>
      (∫ p, (if p.1 ≤ σ ω then K i ω p else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ σ ω then K i ω (t,z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable (fun ω => ∑ i ∈ S, L i ω) P ∧
      (∫ ω, ∑ i ∈ S, L i ω ∂P) = 0 := by sorry
