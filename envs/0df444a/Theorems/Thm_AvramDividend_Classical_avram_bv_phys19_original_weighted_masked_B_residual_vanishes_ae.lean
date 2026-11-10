-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys19_original_weighted_masked_B_residual_vanishes_ae
-- name    : AvramDividend.Classical.avram_bv_phys19_original_weighted_masked_B_residual_vanishes_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:24:57.676387+00:00
-- url     : https://prove2.me/theorems/80a07d46-4bfc-4f70-8b7c-40c0e2d42d83
-- title:
--   Every masked finite-grid BV raw residual coefficient vanishes for the original Lévy source
-- statement:
--   On one full-measure event of the original BV process, the raw residual R(t)=t drift-X_t-J(t) is identically zero; consequently the weighted sum of R(u_i)-R(u_{i+1}) is zero for every finite, possibly stopped or random grid chosen after the path and every real weight sequence. This proves the gradient-weighted R part in the canonical B ledger is zero without any global B integrability premise.
-- source:
--   Direct consequence of authoritative Proved 79a63ca0. Supports literal source residual removal in c5ce01c6, e6a0b83b and e0b94d7f, without replacing the original jump series.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys19_original_weighted_masked_B_residual_vanishes_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ),
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range n,
        a i * (R (u i) - R (u (i + 1)))) = 0 := by sorry
