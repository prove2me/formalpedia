-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_ae_antitone
-- name    : AvramDividend.Classical.avram_bv_residual10_original_clipped_weighted_R_ae_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:43:18.085487+00:00
-- url     : https://prove2.me/theorems/6e43089e-b750-4079-9164-1a5bef509eef
-- title:
--   Higher clipping levels decrease the original BV raw-residual finite-mesh sum
-- statement:
--   For the exact original bounded-variation spectrally negative Levy process, any monotone finite physical mesh and nonnegative path-dependent weights, the signed real raw-residual sum with clipping threshold l is no greater than the same sum with threshold k whenever k <= l. Almost-sure source-exact monotonicity of the original raw R implies every forward R increment is nonpositive. Clipping a nonnegative weight at a larger level only increases that weight, so the signed grid sum decreases. This supplies the a.e. antitone component for a legitimate Fatou or monotone-convergence reduction, but does not assert uniform L1 bounds or the original untruncated theorem.
-- source:
--   AVRAM BV-RESIDUAL10 source-exact clipped raw R monotone convergence interface, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_clipped_weighted_R_ae_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : Ω → ℕ → ℝ)
    (ha : ∀ ω, ∀ i ∈ Finset.range (n + 1), 0 ≤ a ω i)
    (k l : ℝ) (hkl : k ≤ l) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ l then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) ≤
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ k then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) := by sorry
