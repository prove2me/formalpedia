-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_stopping_from_variable_mesh
-- name    : AvramDividend.Classical.avram_ja18_original_stopping_from_variable_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:49:08.087201+00:00
-- url     : https://prove2.me/theorems/cd3512f3-fbb9-45eb-89bd-b8545e45410c
-- title:
--   Original right-continuous bounded stopping times admit finite-valued upper limits under a vanishing mesh certificate
-- statement:
--   Given a deterministic finite-horizon grid for each k, adapted monotone grid times with mesh no larger than δk, exact final horizon n and δk tending to zero, obtain true original continuous-time finite-valued stopping ceilings with τ≤ρk≤n and ρk→τ. Derive bounded natural index via the already-proved original sampled mesh ceiling 1d01e41f, then original stopping by proved sampled-ceiling transfer 7785f280, finite range via Finset.image, convergence via squeeze.
-- source:
--   Independent original-filtration structural child for upper-grid target 40599988; no process representation, no first-moment assumption.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_stopping_from_variable_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (n : ℕ) (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (e : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (δ : ℕ → ℝ≥0)
    (he : ∀ k, Monotone (e k))
    (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k)
    (hTop : ∀ k, e k (N k) = (n : ℝ≥0))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
    (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k, ∃ S : Finset ℝ≥0, ∀ ω, ρ k ω ∈ S) ∧
      (∀ k ω, τ ω ≤ ρ k ω) ∧
      (∀ k ω, ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) := by sorry
