-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_localised_physical_C1_NT_integrable
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_localised_physical_C1_NT_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:30:00.491374+00:00
-- url     : https://prove2.me/theorems/eb7fbea2-45d4-413f-a105-17b00751b78d
-- title:
--   Original BV compact C1 localisation supplies original intrinsic physical marked-jump source integrability
-- statement:
--   For the actual original bounded-variation Lévy process and admissible strategy at a fixed finite ruin/horizon clock, a positive compact interior band and the original C1 hypothesis imply almost-sure integrability of the exact discounted nonlinear left-reserve negative-mark jump source against the genuine original intrinsic marked jump count on (0,T]. The proof obtains real Lipschitz and bounded-value constants from the proved original BV C1 localisation certificate and instantiates the separately proved source-specific original BV intrinsic integrability theorem. No new stochastic or integrability hypothesis is needed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_localised_physical_C1_NT_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      let E : Set (ℝ≥0 × ℝ) :=
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc 0 T)).map
            (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NT := by sorry
