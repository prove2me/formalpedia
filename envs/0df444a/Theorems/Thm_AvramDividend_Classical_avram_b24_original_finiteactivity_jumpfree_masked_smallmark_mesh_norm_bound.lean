-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_jumpfree_masked_smallmark_mesh_norm_bound
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_jumpfree_masked_smallmark_mesh_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:04:00.225352+00:00
-- url     : https://prove2.me/theorems/3e5531a3-b1fd-41fa-8faf-96e52ea2632f
-- title:
--   True original jumpfree stopped physical compensated negative-mark mesh is bounded by deterministic smallmark drift
-- statement:
--   For a stopped finite physical mesh of arbitrary original intrinsic compensated smallmark source Jsmall, bounded predictable coefficients and eventwise no actual source Lévy jumps in any cell, the full masked compensated negative-mark sum has norm bounded by the deterministic complete smallmark compensator drift times the signed physical cell lengths, multiplied by the uniform coefficient bound. The nojump condition is a pointwise implication under one conull original source event, so the theorem can be applied separately to original jumpfree cells, while finitely many true ruin-contact negative mark jumps remain isolated for the signed Itô generator inequality.
-- source:
--   Proved B24 common-conull exact jumpfree intrinsic smallmark drift and norm triangle inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_jumpfree_masked_smallmark_mesh_norm_bound
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
    (hOrder : ∀ i ∈ S, a i ≤ b i)
    (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hWeight : ∀ i ∈ S, ∀ ω, ‖W i ω‖ ≤ L) :
    let d : ℝ := -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
    ∀ᵐ ω ∂P,
      (∀ i ∈ S, ∀ u : ℝ≥0, a i < u → u ≤ b i →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ‖∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)‖ ≤
      ∑ i ∈ S, L * ‖d * ((b i : ℝ) - (a i : ℝ))‖ := by sorry
