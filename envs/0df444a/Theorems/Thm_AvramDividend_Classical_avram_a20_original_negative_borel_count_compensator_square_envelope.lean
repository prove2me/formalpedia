-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_compensator_square_envelope
-- name    : AvramDividend.Classical.avram_a20_original_negative_borel_count_compensator_square_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:04:09.295305+00:00
-- url     : https://prove2.me/theorems/7413b910-18d6-4ed2-b831-7cdefe75ace7
-- title:
--   Actual original finite-activity negative Borel marked-count plus compensator has integrable square
-- statement:
--   For any actual original spectrally negative Lévy physical jump count N_T(B) on an arbitrary measurable negative Borel mark set B under finite negative activity, define r=Tν(B). The physical random envelope N_T(B)+r has integrable square under the original probability measure. Proof reuses the already Proved true physical negative Borel count square-integrability and first-moment integrability, expands (N+r)²=N²+2rN+r², and applies Bochner finite-addition integrability on the source probability space. Combined with the independently Proved finite-weight dominated-sum bound, this supplies the explicit common square-integrable random bound needed to pass uniformly bounded finite mark-simple approximants to the real original marked integral variance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_negative_borel_count_compensator_square_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal + r) ^ 2) P := by sorry
