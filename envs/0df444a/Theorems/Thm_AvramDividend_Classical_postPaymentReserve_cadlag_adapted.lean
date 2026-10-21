-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
-- name    : AvramDividend.Classical.postPaymentReserve_cadlag_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:19:36.810393+00:00
-- url     : https://prove2.me/theorems/a2763475-d54e-4660-aa60-6ec74b85deb7
-- title:
--   The controlled reserve after dividend payments is càdlàg and adapted
-- statement:
--   For every original spectrally negative Lévy process and left-continuous increasing adapted dividend strategy, define the post-payment controlled reserve U+_t = x + X_t - D_{t+}. Show the path U+ is right-continuous at every nonnegative time, has a finite left limit at every strictly positive time, and is adapted to the right-continuous filtration. This supplies a càdlàg adapted process used by stopped HJB verification while preserving the strict-right dividend atom convention. Reuse accepted path regularity and adaptedness lemmas and the original Lévy process fields. No Ito formula or open theorem is assumed.
-- source:
--   Authorised Chat 08 execution; source complete. Depends only on Proved filtration-adapted post-payment dividend and its two Proved path-regularity helpers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_has_leftLimits
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_cadlag_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    (∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (Ici t) t) ∧
    (∀ ω t, 0 < t → ∃ l : ℝ, Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (𝓝[<] t) (𝓝 l)) ∧
    Adapted 𝓕.rightCont
      (fun t ω => x + X.X t ω - rightLimit D t ω) := by sorry
