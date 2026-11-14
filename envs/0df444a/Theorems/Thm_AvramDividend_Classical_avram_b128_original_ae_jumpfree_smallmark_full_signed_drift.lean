-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b128_original_ae_jumpfree_smallmark_full_signed_drift
-- name    : AvramDividend.Classical.avram_b128_original_ae_jumpfree_smallmark_full_signed_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T20:50:51.864468+00:00
-- url     : https://prove2.me/theorems/ddd19597-377b-419d-b428-f66d26b06427
-- title:
--   Original finite-activity conull jumpfree stopped intervals carry exactly the signed full negative-strip compensator drift
-- statement:
--   For the genuine original spectrally negative Levy source with finite negative activity, assume its intrinsic compensated small-mark cutoff limit holds at all times on a single conull event and that actual ordered random stopped intervals are physically jumpfree on a conull event. Proved B80 will supply the exact original signed finite cutoff compensation-only increment on every such interval. B127 then transfers this identity to the correct almost-everywhere original full negative-strip compensator drift using Proved B84 moment convergence. This resolves older B82/B85 overstrong all-path assumptions and supplies a genuine original same-source signed drift input to the positive-clock stopped Ito cash certificate. Publication waits for B80 and B127 to be Proved.
-- source:
--   Proved B80 and B84 original-source theorems with conull pathwise finite cutoff and integral limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine conull jumpfree original stopped intervals carry the signed full negative strip compensator drift. -/

theorem AvramDividend.Classical.avram_b128_original_ae_jumpfree_smallmark_full_signed_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun n : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P,
      Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ)) := by sorry
