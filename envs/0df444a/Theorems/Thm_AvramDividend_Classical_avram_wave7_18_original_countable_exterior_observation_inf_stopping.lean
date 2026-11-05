-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_observation_inf_stopping
-- name    : AvramDividend.Classical.avram_wave7_18_original_countable_exterior_observation_inf_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:52:45.774466+00:00
-- url     : https://prove2.me/theorems/4e7e60dd-8dde-4843-ad4e-d5f3c205cd0b
-- title:
--   Original controlled reserve first strict-band exit among countable real-time observations is a stopping time
-- statement:
--   For the actual original spectrally negative Lévy process with a dividend strategy, define Z_t=x+X.X t-rightLimit D t. Given any deterministic countable times r_k and a band [lower,upper], let σ_k(ω)=r_k if Z_{r_k}(ω)<lower or upper<Z_{r_k}(ω), otherwise σ_k=⊤. The Proved original postPaymentReserve_cadlag_adapted supplies 𝓕.rightCont-adaptation, so the exterior event at r_k is measurable in 𝓕.rightCont(r_k). Its deterministic gated clock σ_k is a stopping time. The pinned IsStoppingTime.iInf for the right-continuous filtration yields that τ(ω)=inf_k σ_k(ω) is an original-filtration stopping time with continuous nonnegative time values. No unrelated probability space is used. This is the countable observed first-exit; equality to the true uncountable-time exit requires a separate right-continuity/density proof, and terminal right-jumps still need handling.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_countable_exterior_observation_inf_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) := by sorry
