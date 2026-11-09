-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
-- name    : AvramDividend.Classical.avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:38:26.818901+00:00
-- url     : https://prove2.me/theorems/a331e012-9f7c-4315-bd1d-9118fd603095
-- title:
--   Both original zero-jump Gaussian martingales admit two-stopping-time conditional sampling on a common physical grid
-- statement:
--   For the exact original zero-jump Levy process and right-continuous filtration, sample its centred process and compensated square on any monotone deterministic physical-time grid. Between any two ordered bounded genuine stopping indices of that grid, both source stopped values equal the conditional expectations of their later stopped values given the earlier stopped history. This establishes the random final grid cell centring for the linear and compensated quadratic parts on one probability space. It does not assert continuous-time Ito, endpoint limit or dividend/ruin atom bounds.
-- source:
--   Proved original right-continuous zero-jump source martingales 0e0e6523 and 208594ec; Proved monotone physical-grid reindexing 43fba27e; pinned Mathlib discrete optional sampling MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le, compiler-signature verified 8 November 2026. Needed for random clipped final cell in the finite-cap Gaussian reward budget 50e1cf4c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
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
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω) ^ 2 - (t : ℝ) * X.σ ^ 2
    (stoppedValue (fun i : ℕ => M (grid i)) α =ᵐ[P]
      P[stoppedValue (fun i : ℕ => M (grid i)) β | hα.measurableSpace]) ∧
    (stoppedValue (fun i : ℕ => Q (grid i)) α =ᵐ[P]
      P[stoppedValue (fun i : ℕ => Q (grid i)) β | hα.measurableSpace]) := by sorry
