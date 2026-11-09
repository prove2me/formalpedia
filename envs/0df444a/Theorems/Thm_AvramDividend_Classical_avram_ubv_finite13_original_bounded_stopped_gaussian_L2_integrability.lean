-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:21:36.81646+00:00
-- url     : https://prove2.me/theorems/de80c263-768a-4b6c-91a2-03bf61d2ab1b
-- title:
--   Original bounded sampled Gaussian stopped values are L2, adapted to stopped history and product integrable
-- statement:
--   On the original zero-negative-jump Levy source, any two ordered bounded genuine stopping indices on a shared physical-time sampling grid yield square-integrable Gaussian centred stopped source values, earlier stopped-history measurability, and integrability of their product. Both integrability and adaptedness are derived from the original source linear and compensated-square martingales, without artificial probability spaces.
-- source:
--   Proved original Gaussian martingales 0e0e6523 and 208594ec, physical reindexer chat03, pinned Mathlib memLp_two_iff_integrable_sq, memLp_stoppedValue, measurable_stoppedValue and Holder integrability. Discharges actual source integrability and measurability side conditions of public Proved cross-moment c3087a6e upstream of finite-cap budget 50e1cf4c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    MemLp (stoppedValue (fun i : ℕ => M (grid i)) α) 2 P ∧
    MemLp (stoppedValue (fun i : ℕ => M (grid i)) β) 2 P ∧
    StronglyMeasurable[hα.measurableSpace]
      (stoppedValue (fun i : ℕ => M (grid i)) α) ∧
    Integrable (fun ω =>
      stoppedValue (fun i : ℕ => M (grid i)) α ω *
      stoppedValue (fun i : ℕ => M (grid i)) β ω) P := by sorry
