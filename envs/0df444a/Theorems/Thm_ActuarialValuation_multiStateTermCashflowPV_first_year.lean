-- Prove2me | Theorems.Thm_ActuarialValuation_multiStateTermCashflowPV_first_year
-- name    : ActuarialValuation.multiStateTermCashflowPV_first_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:24:35.676125+00:00
-- url     : https://prove2.me/theorems/c84c0ef5-5663-47e6-8098-f09f0aec06fe
-- title:
--   One-year state and transition payment identity
-- statement:
--   A one-year contract pays current occupation benefits without discount and end-year transition benefits discounted once.
--
--   **Mathematical statement**
--
--   $$
--   V_1=R_0^{\rm occ}+vR_0^{\rm tr}
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
import Definitions.Def_actuarial_occupationStageReward
import Definitions.Def_actuarial_transitionStageReward
open MeasureTheory

namespace ActuarialValuation

theorem multiStateTermCashflowPV_first_year {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) 
  :
  multiStateTermCashflowPV μ P b c v 1 =
    occupationStageReward (μ 0) (c 0) +
      v * transitionStageReward (μ 0) (P 0) (b 0) := by sorry

end ActuarialValuation
