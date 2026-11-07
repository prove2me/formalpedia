-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget
-- name    : AvramDividend.Classical.avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:13:22.323414+00:00
-- url     : https://prove2.me/theorems/45765042-37eb-48a1-aeda-2df8228fddda
-- title:
--   Original stopped nonnegative paid reward is L1 and budgeted by any integrable centred signed Ito residual
-- statement:
--   For a genuine original Lévy stopped terminal-plus-Stieltjes payoff F and an integrable signed Itô-Meyer residual M, if F is almost-everywhere nonnegative and F ≤ w(x)+M almost everywhere with E[M]≤0, derive both F∈L1 and E[F]≤w(x). This removes an independent L1 premise from the source-residual route and uses no unlocalised uniform integrability.
-- source:
--   Auxiliary source-faithful integrability bridge for fa7052b1 and its HJB budget child e26b843b. The independent physical source proof must provide the genuine original residual, measurability and pathwise inequality; no later theorem is assumed.

import Mathlib

open MeasureTheory

theorem AvramDividend.Classical.avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F M : Ω → ℝ) (b : ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMint : Integrable M P)
    (hSource : ∀ᵐ ω ∂P, F ω ≤ b + M ω)
    (hMmean : (∫ ω, M ω ∂P) ≤ 0) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤ b := by sorry
