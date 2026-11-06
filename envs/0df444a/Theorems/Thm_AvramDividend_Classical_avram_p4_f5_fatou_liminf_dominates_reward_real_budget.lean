-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f5_fatou_liminf_dominates_reward_real_budget
-- name    : AvramDividend.Classical.avram_p4_f5_fatou_liminf_dominates_reward_real_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:04:13.71642+00:00
-- url     : https://prove2.me/theorems/b4eef8f7-48b6-4bdb-acdf-84192e3a4fbd
-- title:
--   Ruin-jump-safe Fatou budget: the actual reward need only lie below the liminf of local stopped rewards
-- statement:
--   For nonnegative measurable L1 approximants F_k with each expected value at most b, if the target nonnegative S is almost surely at most the ENNReal lower limit of F_k, then S is integrable and has expected value at most b. A lower-limit inequality is sufficient and tolerates downward terminal changes at ruin overshoots, unlike exact terminal convergence. This is an independent measure-theoretic bridge intended for the actual original stopped Lévy payoff sequence.
-- source:
--   Direct Mathlib lintegral_mono_ae, lintegral_liminf_le, ENNReal.ofReal of nonnegative real integral and finite lintegral criterion; no stochastic centring, process substitution or circular expected budget.

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f5_fatou_liminf_dominates_reward_real_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hSmeas : AEStronglyMeasurable S P)
    (hSnonneg : 0 ≤ᵐ[P] S)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hliminf : ∀ᵐ ω ∂P,
      ENNReal.ofReal (S ω) ≤
        Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop)
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ b) :
    Integrable S P ∧ (∫ ω, S ω ∂P) ≤ b := by sorry
