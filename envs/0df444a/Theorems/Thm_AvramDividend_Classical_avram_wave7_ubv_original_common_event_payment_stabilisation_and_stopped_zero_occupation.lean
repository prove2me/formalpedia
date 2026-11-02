-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_common_event_payment_stabilisation_and_stopped_zero_occupation
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_common_event_payment_stabilisation_and_stopped_zero_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:48:13.394003+00:00
-- url     : https://prove2.me/theorems/fb083901-99df-41ea-93db-3baadff781b5
-- title:
--   Original UBV common source event for nonmonotone exact payment domains and stopped zero occupation
-- statement:
--   For the actual original X and admissible D, let S_n be arbitrary nonmonotone extended stopping clocks with liminf S_n=top almost surely, and define the same clipped clock sigma_n=min(ruinTime,S_n). One original P-almost-sure event simultaneously supports eventual exact ruin-payment domains at every horizon in an arbitrary countable nonnegative family and sigma-finite mu_n-almost-everywhere strict reserve positivity before every sigma_n, with mu_n allowed to vary by n. The dense/cofinal schedules are exactly those inherited from the previously Proved source zero-occupation theorem; no local-time assertion or new boundary condition is made.
-- source:
--   Proved original countable-horizon domain target 4fd8c76e-b059-4033-88fd-af9cbda41f92 and varying-measures stopped zero-occupation target b08153dc-2799-4b72-ba40-cb10f5a0e285; source zero occupation 6a06830a-160f-45a6-b776-8807e202b19d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_countable_stopped_zero_occupation_variable_time_measures

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_common_event_payment_stabilisation_and_stopped_zero_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (horizons : ℕ → ℝ)
    (hT : ∀ k : ℕ, 0 ≤ horizons k)
    (times radii : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < radii n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, radii n ≤ ε)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ n, SFinite (μ n)) :
    ∀ᵐ ω ∂P,
      (∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩
          Iic (horizons k) =
        paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k)) ∧
      (∀ n : ℕ, ∀ᵐ (t : ℝ≥0) ∂μ n,
        (t : ℝ≥0∞) < min (ruinTime X x D ω) (S n ω) →
          0 < riskProcess X x D t ω) := by sorry
