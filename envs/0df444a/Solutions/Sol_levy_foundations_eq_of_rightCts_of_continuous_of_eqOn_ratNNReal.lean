-- Prove2me | solution 1 for levy_foundations_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:01.404211+00:00
-- url     : https://prove2.me/submissions/a410e62e-661c-48b6-a288-96f0c60ea644

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Definitions.Def_levy_foundations_ceilApprox

open Filter Topology
open scoped NNReal

theorem solution
    {β : Type*} [TopologicalSpace β] [T2Space β]
    {f g : ℝ≥0 → β}
    (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hg : Continuous g)
    (heq : ∀ (k n : ℕ),
      f ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) =
      g ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))) :
    f = g := by
  funext t
  set q : ℕ → ℝ≥0 := fun m => ((⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℕ) : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) with hq
  have hlow : ∀ m, t ≤ q m := by
    intro m
    have hm : (0 : ℝ≥0) < ((m + 1 : ℕ) : ℝ≥0) := by positivity
    rw [hq]; dsimp only
    rw [le_div_iff₀ hm]
    have : (t : ℝ) * ↑(m + 1) ≤ (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast this
  have hup : ∀ m, q m ≤ t + 1 / ((m + 1 : ℕ) : ℝ≥0) := by
    intro m
    have hm : (0 : ℝ≥0) < ((m + 1 : ℕ) : ℝ≥0) := by positivity
    rw [hq]; dsimp only
    rw [div_le_iff₀ hm, add_mul, one_div, inv_mul_cancel₀ hm.ne']
    have h1 : ((⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) * ↑(m + 1) + 1 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ (t : ℝ) * ↑(m + 1) by positivity)
      exact this.le
    exact_mod_cast h1
  have hlim : Filter.Tendsto q Filter.atTop (𝓝 t) := by
    have h2 : Filter.Tendsto (fun m : ℕ => t + 1 / ((m + 1 : ℕ) : ℝ≥0)) Filter.atTop (𝓝 t) := by
      have : Filter.Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ≥0)) Filter.atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)
      simpa using (tendsto_const_nhds (x := t)).add this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 hlow hup
  have hlim' : Filter.Tendsto q Filter.atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hlow⟩
  have h1 : Filter.Tendsto (f ∘ q) Filter.atTop (𝓝 (f t)) := (hf t).tendsto.comp hlim'
  have h2 : Filter.Tendsto (g ∘ q) Filter.atTop (𝓝 (g t)) := (hg.tendsto t).comp hlim
  have h3 : f ∘ q = g ∘ q := funext fun m => heq _ m
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2
