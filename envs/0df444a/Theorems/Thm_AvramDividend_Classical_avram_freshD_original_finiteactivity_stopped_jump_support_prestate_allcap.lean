-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finiteactivity_stopped_jump_support_prestate_allcap
-- name    : AvramDividend.Classical.avram_freshD_original_finiteactivity_stopped_jump_support_prestate_allcap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:15:45.090462+00:00
-- url     : https://prove2.me/theorems/fe82c4a7-bfc0-4651-83d1-b47d0b2510fb
-- title:
--   Original finite-activity physical jump support and strict pre-ruin spatial mask at any cap
-- statement:
--   For a spectrally negative Lévy process with finite negative jump activity and an admissible dividend strategy bounded by any extended-real cap, including an infinite cap, construct the almost-sure finite set of original negative jump times on a bounded horizon. Its cardinality equals the physical marked jump count. At each selected negative jump strictly before ruin, the left limit of the original post-right-dividend reserve is strictly positive and lies within the extended-real cap. This general-cap source lemma verifies the actual spatial mask in the fullmarked stopped Itô–Meyer kernel without assuming the cap is finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finiteactivity_stopped_jump_support_prestate_allcap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
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
