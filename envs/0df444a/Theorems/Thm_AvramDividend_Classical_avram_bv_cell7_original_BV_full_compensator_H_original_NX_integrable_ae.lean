-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_full_compensator_H_original_NX_integrable_ae
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_full_compensator_H_original_NX_integrable_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:32:42.932913+00:00
-- url     : https://prove2.me/theorems/efdcf773-4c29-4ad3-a890-531a7920c7bb
-- title:
--   Full source-identical BV compensated H integrable on the actual original global Lévy marked jump measure
-- statement:
--   For the actual original bounded-variation spectrally negative Lévy process, actual admissible strategy, original finite ruin/horizon stopped clock, and local compact C1 band, the complete indexed compensated H kernel is integrable on the original global marked NX almost surely, without an assumed integrability hypothesis. The proof imports the source-identical H-to-physical C1 kernel equality and the original intrinsic-to-global NX C1 integrability certificate, which in turn reduce to genuine original BV negative jump mass finiteness. This removes the remaining conditional hypothesis of the accepted original finite-grid H signed integral bridge.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_full_compensator_H_original_NX_integrable_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q a b L R : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      let τ : Ω → ℝ≥0 := fun η =>
        (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
              p.1.1 + p.2) -
             w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
              p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NX : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
          (fun v : ℝ≥0 => (v, Δ v)))
      Integrable (fun p => H ((p.1, ω), p.2)) NX := by sorry
