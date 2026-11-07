-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_measurable_path_version
-- name    : AvramDividend.Classical.avram_bv_jump8_source_cutoff_measurable_path_version
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T17:57:52.211325+00:00
-- url     : https://prove2.me/theorems/b879a7b0-546f-47c3-89b6-41d84d04f8bc
-- title:
--   Source-exact bounded measurable path version for the intrinsic cutoff marked-jump exponential
-- statement:
--   For each n and strict negative cutoff k, construct an actual bounded [0,1]-valued Borel measurable functional of the entire Lévy path whose values agree almost surely with both the intrinsic original marks in (0,1] and the shifted-original marks in (n,n+1]. The functional must be constructed by source-càdlàg measurable approximations; an arbitrary all-path raw left-limit extractor is not assumed measurable. This is the missing source-specific bridge to already-Proved full-path stationary law.
-- source:
--   Derive by dyadic/grid jump-size cutoff approximations and source càdlàg path law, using Proved left-limit translation 81fc4187 and original finite-cutoff integrability 6fd5d9c9. Proved shifted path law f7f7d00c and measurable shifted path 8b9eb23c then give the desired expected stationary weighted transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_source_cutoff_measurable_path_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ), ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧ (∀ f, 0 ≤ F f ∧ F f ≤ 1) ∧
      (∀ᵐ ω ∂P, F (fun t : ℝ≥0 => X.X t ω) =
        Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) ∧
      (∀ᵐ ω ∂P,
        F (fun t : ℝ≥0 => X.X ((n : ℝ≥0) + t) ω - X.X (n : ℝ≥0) ω) =
        Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) := by sorry
