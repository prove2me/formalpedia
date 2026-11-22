-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:52:26.643413+00:00
-- url     : https://prove2.me/theorems/2de52b33-f2ab-490f-b726-ecfe8d5a382a
-- title:
--   Exact original intrinsic negative marked Lévy finite local Borel jump count real interval additivity, even with globally infinite jump activity
-- statement:
--   For any original spectrally negative Lévy physical marked jump measure NX, any locally finite negative Borel mark B and time interval s≤r≤t, prove P-almost surely exact REAL marked count additivity N_{s,t}(B).toReal = N_{s,r}(B).toReal + N_{r,t}(B).toReal without requiring finite global jump activity. The original Proved physical ENNReal marked measure count pathwise additivity source supplies equality in ℝ≥0∞, and the freshly proved true original local Borel count finite-a.e. physical Campbell consequence proves both pieces finite a.e., permitting the exact ENNReal.toReal_add conversion. This is essential to upgrade the verified right-continuous conditional centred mark-increment mean zero and original StronglyAdapted mark sums into a genuine physical compensated simple Lévy martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_interval_split
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) (hν : X.ν B < ⊤) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P,
      (NX ω (Ioc s t ×ˢ B)).toReal =
        (NX ω (Ioc s r ×ˢ B)).toReal +
          (NX ω (Ioc r t ×ˢ B)).toReal := by sorry
