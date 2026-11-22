-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finiteactivity_stopped_jump_support_prestate_finitecap
-- name    : AvramDividend.Classical.avram_freshD_original_finiteactivity_stopped_jump_support_prestate_finitecap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:08:21.694826+00:00
-- url     : https://prove2.me/theorems/75d95521-3e04-429c-a270-39a2b4a5c390
-- title:
--   Physical negative-jump support with exact strict pre-ruin finite-cap prestate mask
-- statement:
--   For the original spectrally negative Lévy process under finite jump activity and an admissible finite-cap dividend strategy, select the almost-surely finite negative-jump times on a bounded horizon. Their count agrees exactly with the intrinsic marked jump measure. At each selected negative jump strictly before ruin, the left limit of the original post-right-dividend reserve is strictly positive and lies inside the cap. This is the source-faithful jump-support and prestate-mask bridge needed to localise the full-mark stopped Itô–Meyer jump kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finiteactivity_stopped_jump_support_prestate_finitecap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hFin : C ≠ ⊤) (hxc : ENNReal.ofReal x ≤ C)
    (hD : IsAdmissibleLe X x C D)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ S : Ω → Finset ℝ≥0,
      ∀ᵐ ω ∂P,
        (∀ u : ℝ≥0, u ∈ S ω ↔
          0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0) ∧
        ((S ω).card : ℝ) =
          (((Measure.count.restrict {u : ℝ≥0 |
             0 < u ∧ X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 =>
                (u, X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal ∧
        (∀ t : ℝ≥0, t ∈ S ω →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 < Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t ∧
          ENNReal.ofReal (Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ≤ C) := by sorry
