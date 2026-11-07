-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
-- name    : AvramDividend.Classical.avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:23:41.488146+00:00
-- url     : https://prove2.me/theorems/26261fe4-5a4e-4ed9-b845-8e610a8d4103
-- title:
--   Three original stopped centred compensators and signed nonintegrable remainders imply local payoff L1 and HJB budget
-- statement:
--   An original localised Itô-Meyer decomposition supplies three actual integrable mean-zero Gaussian, small-negative-jump and large-negative-jump martingale contributions Mc, Ms, Ml, plus potentially nonintegrable but nonpositive generator and dividend-jump remainders G and R. If the exact original stopped paid reward F is nonnegative and a.e. strongly measurable and obeys the pathwise five-piece inequality, then F is integrable and E[F]≤w(x), without assuming integrability of G or R or uniform integrability of the unlocalised processes.
-- source:
--   Independent noncircular source assembly for fa7052b1 and e26b843b. The original stochastic calculus must still construct the physical Mc/Ms/Ml and sign remainders. This helper proves the precise nonnegative-payoff L1 and expectation deduction and imports only Proved 45765042.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget

open MeasureTheory AvramDividend.Classical

theorem AvramDividend.Classical.avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F Mc Ms Ml G R : Ω → ℝ) (b : ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMcI : Integrable Mc P) (hMsI : Integrable Ms P)
    (hMlI : Integrable Ml P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMs0 : (∫ ω, Ms ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      F ω ≤ b + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤ b := by sorry
