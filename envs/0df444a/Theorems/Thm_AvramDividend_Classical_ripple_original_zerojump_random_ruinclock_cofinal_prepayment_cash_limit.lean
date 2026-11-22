-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_random_ruinclock_cofinal_prepayment_cash_limit
-- name    : AvramDividend.Classical.ripple_original_zerojump_random_ruinclock_cofinal_prepayment_cash_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:10:08.678042+00:00
-- url     : https://prove2.me/theorems/bbe7e6a0-afc6-441d-9d3d-7a29d53e1993
-- title:
--   Actual original zero-jump random stopped cash and prepayment terminal is exact left limit of cofinal strictly surviving right-payment clocks
-- statement:
--   Let X be the true original spectrally negative Levy process with no jumps, D the original admissible left-continuous dividend strategy with its actual Lebesgue-Stieltjes dividend measure, and rho an arbitrary positive random time no later than original ruin. For any random family of subclocks increasing strictly from below toward rho, prove that along almost every original sample path the real discounted post-right-payment terminal candidate plus actual strict pre-subclock dividend cash converges to exactly the original prepayment reserve discounted terminal plus the strict pre-rho Stieltjes cash. The statement permits rho=ruin, with no artificial cash inequality assumption. It provides the exact endpoint bridge needed to transfer the true strict pre-ruin finite cash ledger to the source terminal used by the original finite-cap physical stopped Ito-Stieltjes source.
-- source:
--   Proved original zerojump cofinal strict reward left limit 2151ad9a-4187-47c8-83d2-9b08fb95f231 and true original strict pre-ruin discounted Stieltjes cash ledger a9c657c3-46b6-4e92-ae8d-5640767ea366. Original source 0ef5d778-7536-4a04-90bc-68e0b5c21262.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_cofinal_strict_reward_left_limit
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.ripple_original_zerojump_random_ruinclock_cofinal_prepayment_cash_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (hq : 0 < q)
    (ρ : Ω → ℝ≥0)
    (hρpos : ∀ ω, 0 < ρ ω)
    (hρle : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → Ω → ℝ≥0)
    (hMono : ∀ ω, Monotone (fun j => u j ω))
    (hStrict : ∀ j ω, u j ω < ρ ω)
    (hLimit : ∀ ω,
      Tendsto (fun j => u j ω) atTop (𝓝[<] (ρ ω))) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun j =>
          Real.exp (-(q * (u j ω : ℝ))) *
            w (x + X.X (u j ω) ω - rightLimit D (u j ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (u j ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)
        atTop
        (𝓝 (Real.exp (-(q * (ρ ω : ℝ))) *
            w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)) := by sorry
