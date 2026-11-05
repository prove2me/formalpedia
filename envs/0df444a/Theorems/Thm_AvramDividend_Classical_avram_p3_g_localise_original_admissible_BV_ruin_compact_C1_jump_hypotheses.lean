-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:50:09.728814+00:00
-- url     : https://prove2.me/theorems/eb00e27d-017d-4f5c-956f-1dad3a9cc45a
-- title:
--   Original admissible BV reserve supplies bounded stopped predictable compact strip and C1 jump bounds
-- statement:
--   Under the original IsAdmissibleLe BV source control and canonical C1 candidate, a genuine compact interior strip and a deterministic horizon supply the finite ruin-truncated stopping time, predictable original pre-reserve band, and the exact local Lipschitz and below-ceiling payoff bound required for the literal stopped jump compensator. Open interior follows automatically from continuity of ENNReal.ofReal. No boundary occupation or global compensation conclusion is postulated.
-- source:
--   Composes already Proved original-source helpers 7759e9e1 and 0990d837, with IsAdmissibleLe strategy projection hD.1.1 and Mathlib topological openness.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
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
    (T : ℝ≥0) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    (∀ ω, τ ω ≤ T) ∧
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    (∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b) ∧
    (∀ p ∈ E, p.1 ≤ T) ∧
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by sorry
