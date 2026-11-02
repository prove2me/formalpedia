-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_nonmonotone_tailinf_stopping_localiser_package
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_tailinf_stopping_localiser_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:47:20.855753+00:00
-- url     : https://prove2.me/theorems/407b67dc-9d48-4578-9613-0c8a4592ba19
-- title:
--   Original nonmonotone ruin-clipped tail-infimum source stopping-localiser package
-- statement:
--   For the actual original source SpectrallyNegativeLevy P 𝓕 and admissible D, let S_n be arbitrary genuine 𝓕.rightCont stopping clocks, not assumed monotone, with liminf S_n=∞ P-a.s. Define τ_n as the tail infimum of later S clocks clipped at actual ruin. Simultaneously prove each τ_n is an original right-continuous stopping time, the family is monotone for every sample path, each τ_n≤ruinTime pathwise, and sup τ_n=ruinTime almost surely including zero and infinity. Reuse Proved clock/stopping identities without adding any boundary, smoothness, bounded variation, atomlessness or filtration assumption. This is a localiser geometry theorem, not an Itô–Meyer or dividend Stieltjes proof.
-- source:
--   Accepted original tail-inf stopping result dae08fbd-1984-4610-8a6c-4d6acc3e1a75 and original ruin endpoint liminf identity b6f6314c-f08c-4ac7-987f-77eeccb7e5fd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_tailinf_stopping_localiser_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ ω, Monotone
      (fun n : ℕ => ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ n ω, (⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) ≤
      ruinTime X x D ω) ∧
    (∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) =
      ruinTime X x D ω) := by sorry
