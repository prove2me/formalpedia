-- Prove2me | Theorems.Thm_ActuarialValuation_multiStateTermCashflowPV_decompose
-- name    : ActuarialValuation.multiStateTermCashflowPV_decompose
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:19:50.058497+00:00
-- url     : https://prove2.me/theorems/e20c7f05-3eeb-4575-8bc3-3e28c4b093f6
-- title:
--   State and transition EPVs separate additively
-- statement:
--   Expected present value decomposes into beginning-year state annuity and end-year transition benefit terms.
--
--   **Mathematical statement**
--
--   $$
--   V_n=V_n^{\rm occ}+V_n^{\rm tr}
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
import Definitions.Def_actuarial_occupationStageReward
import Definitions.Def_actuarial_transitionStageReward
open MeasureTheory

namespace ActuarialValuation

theorem multiStateTermCashflowPV_decompose {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) (n : ℕ)
  :
  multiStateTermCashflowPV μ P b c v n =
    (∑ k ∈ Finset.range n, v ^ k * occupationStageReward (μ k) (c k)) +
    (∑ k ∈ Finset.range n, v ^ (k + 1) * transitionStageReward (μ k) (P k) (b k)) := by sorry

end ActuarialValuation
