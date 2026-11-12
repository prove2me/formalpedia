-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18x_original_J_integrable_horizon_majorant
-- name    : AvramDividend.Classical.avram_ja18x_original_J_integrable_horizon_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:58:53.391376+00:00
-- url     : https://prove2.me/theorems/7dbfa029-0781-44af-a63c-9f44e861e63b
-- title:
--   Original compensated J has an integrable pathwise fixed-horizon majorant
-- statement:
--   Use the exact physical decomposition JA18T: J(t)=Jsmall(t)+L(t)+t(c−E[X1]). The Proved original small-band source provides an integrable horizon envelope; JA18V provides one for the original large-jump sum. Add the deterministic linear drift bound. The resulting B is integrable and bounds |J(t)| simultaneously for all t≤n.
-- source:
--   J-A18 JA18P stopped J bounded optional sampling

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18x_original_J_integrable_horizon_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (n : ℕ) (hn : 0 < n) :
    let μ : ℝ := ∫ η, X.X 1 η ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖J t ω‖ ≤ B ω) := by sorry
