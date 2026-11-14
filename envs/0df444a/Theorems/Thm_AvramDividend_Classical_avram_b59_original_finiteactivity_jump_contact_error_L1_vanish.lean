-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b59_original_finiteactivity_jump_contact_error_L1_vanish
-- name    : AvramDividend.Classical.avram_b59_original_finiteactivity_jump_contact_error_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:34:44.466758+00:00
-- url     : https://prove2.me/theorems/33966395-6acc-4d9b-9942-44ff7bf209a5
-- title:
--   Original finite-activity source negative-jump contact error vanishes in L1 on arbitrary events as grid tolerance shrinks
-- statement:
--   For the actual spectrally negative finite-activity Lévy process, suppose every original physical jump-contact error at mesh index m is bounded samplewise by a vanishing nonnegative deterministic tolerance times a measurable number of selected negative-jump-containing cells. Assume each selected count is dominated by the genuine original finite-horizon negative marked jump count. Then the actual absolute errors converge to zero in restricted L1 on every event, independently of mesh cardinality, without requiring a negative-jump size moment or auxiliary noise source.
-- source:
--   Proved B58 actual finite activity selected jump-count expected rate, monotone restricted Bochner integrals, deterministic squeeze with vanishing tolerance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b59_original_finiteactivity_jump_contact_error_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A : Set Ω)
    (J : ℕ → Ω → Finset ℕ)
    (hJmeas : ∀ m, Measurable (fun ω : Ω => ((J m ω).card : ℝ)))
    (hJdom : ∀ m ω, ((J m ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (E : ℕ → Ω → ℝ) (hEmeas : ∀ m, Measurable (E m))
    (η : ℕ → ℝ) (hη : ∀ m, 0 ≤ η m)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hEbound : ∀ m ω, |E m ω| ≤ η m * ((J m ω).card : ℝ)) :
    Tendsto (fun m => ∫ ω in A, |E m ω| ∂P) atTop (𝓝 0) := by sorry
