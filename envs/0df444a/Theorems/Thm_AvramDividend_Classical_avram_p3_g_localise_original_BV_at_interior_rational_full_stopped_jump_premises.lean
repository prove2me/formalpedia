-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_at_interior_rational_full_stopped_jump_premises
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_BV_at_interior_rational_full_stopped_jump_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:27:05.653132+00:00
-- url     : https://prove2.me/theorems/4970d581-1d77-4c45-bda7-45374c4de4fd
-- title:
--   Canonical BV source at strict interior point supplies rational stopped predictable C1 compensation bounds
-- statement:
--   Given only the actual X.BoundedVariation, source IsAdmissibleLe, canonical C1 verification candidate and any interior reserve y, select rational endpoints a,b with a<=2 and a strict open neighbourhood around y. The original stopped ruin time, predictable compact pre-reserve region, hEm, hEregion, local Lipschitz and below-ceiling payoff bounds follow automatically on this band. This supplies all localisation-side premises of the original stopped literal jump theorem, with source kernel and Levy intensity obligations still explicitly separate.
-- source:
--   Composes public Proved P3-G rational cover 3abce49a and original source admissible stopped C1 bundle eb00e27d; no terminal limit or compensation conclusion assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_BV_at_interior_rational_full_stopped_jump_premises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (T : ℝ≥0) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    ∃ a b : ℚ, 0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
      (a : ℝ) ≤ (b : ℝ) ∧ y ∈ Ioo (a : ℝ) (b : ℝ) ∧
      (let τ : Ω → ℝ≥0 := fun ω =>
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
       let E : Set (ℝ≥0 × Ω) := {p |
         (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
         Function.leftLim
           (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
             Icc (a : ℝ) (b : ℝ)}
       (∀ ω, τ ω ≤ T) ∧
       IsStoppingTime 𝓕.rightCont
         (fun ω => (τ ω : WithTop ℝ≥0)) ∧
       MeasurableSet[𝓕.rightCont.predictable] E ∧
       (∀ p ∈ E, Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
           Icc (a : ℝ) (b : ℝ)) ∧
       (∀ p ∈ E, p.1 ≤ T) ∧
       ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
         (∀ u ∈ Icc ((a : ℝ) / 2) (b : ℝ),
           ∀ v ∈ Icc ((a : ℝ) / 2) (b : ℝ),
           |w u - w v| ≤ L * |u - v|) ∧
         (∀ v : ℝ, v ≤ (b : ℝ) → |w v| ≤ R)) := by sorry
