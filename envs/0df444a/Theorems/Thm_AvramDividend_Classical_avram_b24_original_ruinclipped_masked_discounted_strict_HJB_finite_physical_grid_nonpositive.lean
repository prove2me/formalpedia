-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_masked_discounted_strict_HJB_finite_physical_grid_nonpositive
-- name    : AvramDividend.Classical.avram_b24_original_ruinclipped_masked_discounted_strict_HJB_finite_physical_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:52:35.0202+00:00
-- url     : https://prove2.me/theorems/46f398c5-ab30-4761-8535-e9c3c624fa11
-- title:
--   True original ruin-clipped finite physical cells have a nonpositive masked discounted HJB generator residual
-- statement:
--   For the original spectrally negative Lévy source X with HJB generator inequality X.generator w-qw≤0 on the positive strict cap interior and any finite ordered physical grid of deterministic or realised sample-path cells, allow an arbitrary Boolean ACTIVE mask, such as the original ruin-clipped pre-left cell condition. Assume only active cells have a reserve point strictly inside (0,C). The discounted real HJB residual contribution at any active cell is nonpositive because exp(-q s_i)>0, elapsed time ≥0 and the true original generator drift ≤0; inactive cells contribute exactly zero even if their postruin reserves lie outside the HJB domain. Therefore the full masked physical grid generator contribution is nonpositive. This safely preserves the ruin clipping and source generator sign without evaluating HJB assumptions postruin. It is the appropriate strict-interior drift-sign building block for the genuine B219 original discounted Ito-Meyer cash ledger; true right dividends, mark/Gaussian stochastic noise, terminal ruin contact and source integrability remain separate obligations.
-- source:
--   Actual original Levy generator strict HJB inequality and finite Boolean clipped interior physical cell sum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_ruinclipped_masked_discounted_strict_HJB_finite_physical_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (y : ι → ℝ) (active : ι → Bool)
    (hTimes : ∀ i ∈ S, s i ≤ t i)
    (hInterior : ∀ i ∈ S, active i = true →
      0 < y i ∧ ENNReal.ofReal (y i) < C) :
    (∑ i ∈ S, if active i then
      Real.exp (-(q * (s i : ℝ))) *
        ((t i : ℝ) - (s i : ℝ)) *
        (X.generator w (y i) - q * w (y i))
      else 0) ≤ 0 := by sorry
