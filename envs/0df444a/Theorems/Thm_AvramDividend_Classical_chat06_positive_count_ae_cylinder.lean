-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_positive_count_ae_cylinder
-- name    : AvramDividend.Classical.chat06_positive_count_ae_cylinder
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T15:52:54.130985+00:00
-- url     : https://prove2.me/theorems/99d31ac1-c5c4-42c5-96d1-5b970b70a8da
-- title:
--   Positive count as an almost-sure arrival-time cylinder
-- statement:
--   The positive count event equals its adjacent arrival-threshold cylinder up to a probability-null event under almost-sure nonexplosion and monotonicity.
-- source:
--   Verified source complete private candidate at pinned Mathlib revision; source and remote job recorded in Chat 06 SUBMISSIONS.json. Preamble defines the local arrival/prefix functions used by exact statement.

import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Poisson.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
namespace AvramChat06

def arrivalForPoissonAE {Ω : Type*} (τ : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), τ i ω

noncomputable def countForPoissonAE {Ω : Type*}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t < arrivalForPoissonAE τ n ω}

end AvramChat06
open AvramChat06

theorem AvramDividend.Classical.chat06_positive_count_ae_cylinder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun k =>
      arrivalForPoissonAE τ k ω) atTop atTop)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun k =>
      arrivalForPoissonAE τ k ω)) :
    {ω | countForPoissonAE τ t ω = n + 1} =ᵐ[P]
      ({ω | t < arrivalForPoissonAE τ (n + 1) ω} \
       {ω | t < arrivalForPoissonAE τ n ω}) := by sorry
