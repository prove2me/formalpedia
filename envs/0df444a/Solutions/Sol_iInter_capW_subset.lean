-- Prove2me | solution 1 for iInter_capW_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:27.694378+00:00
-- url     : https://prove2.me/submissions/3affe0fb-3b97-463e-8ac3-351fc1fdfd57

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_isCompact_capBelow

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) (β : ℕ → ℕ) :
    (⋂ n, capW π β n) ⊆ π '' capBelow β := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable Z
  intro y hy
  -- for each n, obtain a normalized bounded prefix sₙ with y ∈ closure (π '' N_{sₙ,n})
  have hsel : ∀ n : ℕ, ∃ s ∈ capSeqs β n, y ∈ capScheme π s n := by
    intro n
    have := mem_iInter.mp hy n
    simpa only [capW, mem_iUnion, exists_prop] using this
  choose s hs hys using hsel
  -- for each n, pick τₙ in the cylinder with π τₙ within 1/(n+1) of y
  have hτ : ∀ n : ℕ, ∃ τ ∈ PiNat.cylinder (s n) n, dist y (π τ) < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨z, hz_mem, hz_dist⟩ := Metric.mem_closure_iff.mp (hys n) _ hpos
    obtain ⟨τ, hτ_mem, rfl⟩ := hz_mem
    exact ⟨τ, hτ_mem, hz_dist⟩
  choose τ hτ_mem hτ_dist using hτ
  -- τₙ is bounded by β on the first n coordinates
  have hτ_bdd : ∀ n, ∀ i < n, τ n i ≤ β i := by
    intro n i hi
    have h1 : τ n i = s n i := hτ_mem n i hi
    rw [h1]
    exact (hs n).1 i hi
  -- clip to Σ(β) and extract a convergent subsequence
  set ρ : ℕ → (ℕ → ℕ) := fun n => fun i => min (τ n i) (β i) with hρ
  have hρ_mem : ∀ n, ρ n ∈ capBelow β := fun n i => min_le_right _ _
  obtain ⟨σ, hσ_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    (isCompact_capBelow β).tendsto_subseq hρ_mem
  -- τ ∘ φ converges pointwise to σ (eventually agrees with ρ ∘ φ)
  have hτφ_tendsto : Tendsto (fun j => τ (φ j)) atTop (𝓝 σ) := by
    rw [tendsto_pi_nhds]
    intro i
    have hρi : Tendsto (fun j => ρ (φ j) i) atTop (𝓝 (σ i)) :=
      (tendsto_pi_nhds.mp hφ_tendsto) i
    apply hρi.congr'
    filter_upwards [Filter.eventually_ge_atTop (i + 1)] with j hj
    have hij : i < φ j := lt_of_lt_of_le (Nat.lt_succ_self i) (hj.trans (hφ_mono.le_apply))
    simp only [hρ]
    exact min_eq_left (hτ_bdd (φ j) i hij)
  -- π (τ (φ j)) → π σ, but also π (τ n) → y; conclude y = π σ
  have h1 : Tendsto (fun j => π (τ (φ j))) atTop (𝓝 (π σ)) :=
    (hπ.tendsto σ).comp hτφ_tendsto
  have h2 : Tendsto (fun n => π (τ n)) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => dist_nonneg)
      (fun n => le_of_lt (by rw [dist_comm]; exact hτ_dist n))
  have h2φ : Tendsto (fun j => π (τ (φ j))) atTop (𝓝 y) :=
    h2.comp hφ_mono.tendsto_atTop
  exact ⟨σ, hσ_mem, tendsto_nhds_unique h1 h2φ⟩
