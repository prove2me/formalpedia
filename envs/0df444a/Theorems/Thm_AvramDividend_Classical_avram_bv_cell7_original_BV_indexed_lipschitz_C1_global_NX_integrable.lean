-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_indexed_lipschitz_C1_global_NX_integrable
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_lipschitz_C1_global_NX_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:45:14.223522+00:00
-- url     : https://prove2.me/theorems/246a10a2-48c9-44eb-acde-0060e035c11f
-- title:
--   One common original BV full-measure event supports all compact Lipschitz C1 jump-source integrals
-- statement:
--   For the actual bounded-variation Lévy process and original admissible dividend strategy, countably many independently bounded compact C1 source bands have their original discounted stopped nonlinear negative-jump kernels simultaneously integrable against the genuine global original Lévy marked NX, on one full-measure sample-path event valid for every physical horizon. Local deterministic band bounds are genuine explicit hypotheses, each discharged by the accepted original BV C1 global NX integrability certificate. The proof combines the distinct original null sets via the exact pinned Mathlib countable almost-everywhere theorem, without surrogate stochastic processes or assumed compensated-source identities.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_lipschitz_C1_global_NX_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hLip : ∀ n, ∀ u ∈ Icc (a n / 2) (b n),
      ∀ v ∈ Icc (a n / 2) (b n),
      |w u - w v| ≤ L n * |u - v|)
    (hWbound : ∀ n, ∀ v : ℝ, v ≤ b n → |w v| ≤ R n) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ T : ℝ≥0,
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      let E : Set (ℝ≥0 × ℝ) :=
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NX : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
          (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NX := by sorry
