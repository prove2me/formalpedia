-- Prove2me | solution 1 for exists_eps_optimal_selector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:56.631175+00:00
-- url     : https://prove2.me/submissions/815da51b-eb6c-4f4f-b043-30232190bc48

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Theorems.Thm_iInf_fiber_lt
import Theorems.Thm_exists_fallback_selector
import Theorems.Thm_exists_level_selector
import Theorems.Thm_AnalyticallyMeasurable_find
import Theorems.Thm_EpsOptimalSelection_exists_band
import Theorems.Thm_EpsOptimalSelection_band_lower_bound
import Theorems.Thm_IsLowerSemianalytic_iInf_fiber
import Theorems.Thm_MeasureTheory_AnalyticSet_compl_mem_analyticMeasurableSpace
import Theorems.Thm_MeasureTheory_AnalyticSet_mem_analyticMeasurableSpace


set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
open EpsOptimalSelection
theorem _root_.solution [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ (∀ h, (h, φ h) ∈ Γ) ∧
      ∀ h, F (h, φ h) ≤ (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) + ε := by
  rcases isEmpty_or_nonempty H with hH | hH
  · -- degenerate domain: everything is vacuous
    haveI := hH
    letI : MeasurableSpace H := analyticMeasurableSpace H
    letI : MeasurableSpace E := borel E
    exact ⟨fun h => isEmptyElim h, measurable_of_empty _,
      fun h => isEmptyElim h, fun h => isEmptyElim h⟩
  · obtain ⟨h₀⟩ := hH
    have hΓne : Γ.Nonempty := ⟨(h₀, (hfib h₀).choose), (hfib h₀).choose_spec⟩
    -- Step 1: normalized tolerance ε' = min ε 1 (positive, finite, ≤ ε)
    set ε' : ℝ≥0∞ := min ε 1 with hε'def
    have hε'0 : 0 < ε' := lt_min hε zero_lt_one
    have hε'top : ε' ≠ ∞ := ((min_le_right ε 1).trans_lt one_lt_top).ne
    have hε'ε : ε' ≤ ε := min_le_left ε 1
    -- Step 2: the fiber infimum is lower semianalytic (BS 7.47)
    set g : H → ℝ≥0∞ := fun h => ⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)
      with hgdef
    have hg : IsLowerSemianalytic g := IsLowerSemianalytic.iInf_fiber hΓ hF
    -- Step 3: the selector family — fallback plus one selector per level
    obtain ⟨φ₀, hφ₀meas, hφ₀Γ⟩ := exists_fallback_selector hΓ hΓne hfib
    have hlevel : ∀ m : ℕ, ∃ χ : H → E, AnalyticallyMeasurable χ ∧
        ∀ h : H, (∃ e, (h, e) ∈ Γ ∧ F (h, e) < (m : ℝ≥0∞) * ε') →
          (h, χ h) ∈ Γ ∧ F (h, χ h) < (m : ℝ≥0∞) * ε' :=
      fun m => exists_level_selector hΓ hF hφ₀meas _
    choose χ hχmeas hχsel using hlevel
    set ψ : ℕ → H → E := fun m => match m with
      | 0 => φ₀
      | m + 1 => χ (m + 1) with hψdef
    have hψmeas : ∀ m, AnalyticallyMeasurable (ψ m) := by
      intro m
      cases m with
      | zero => exact hφ₀meas
      | succ m => exact hχmeas (m + 1)
    -- Step 4: the band predicate is σ(Σ¹₁)-measurable
    have hp : ∀ m, @MeasurableSet H (analyticMeasurableSpace H)
        {h | bandPred ε' m (g h)} := by
      intro m
      cases m with
      | zero =>
        have hset : {h : H | bandPred ε' 0 (g h)} = {h : H | g h < ⊤}ᶜ := by
          ext h
          show g h = ∞ ↔ ¬ g h < ⊤
          simp [lt_top_iff_ne_top]
        rw [hset]
        exact (hg ⊤).compl_mem_analyticMeasurableSpace
      | succ m =>
        have hset : {h : H | bandPred ε' (m + 1) (g h)}
            = {h : H | g h < ((m + 1 : ℕ) : ℝ≥0∞) * ε'} := rfl
        rw [hset]
        exact (hg _).mem_analyticMeasurableSpace
    have hex : ∀ h, ∃ m, bandPred ε' m (g h) := fun h =>
      exists_band hε'0 hε'top (g h)
    -- Steps 5–6: glue with Nat.find; correctness by cases on the band
    have hcorrect : ∀ h : H, (h, ψ (Nat.find (hex h)) h) ∈ Γ ∧
        F (h, ψ (Nat.find (hex h)) h) ≤ g h + ε' := by
      intro h
      rcases hfind : Nat.find (hex h) with _ | m
      · -- the infinite band: any feasible selection is trivially optimal
        have hspec : bandPred ε' 0 (g h) := by
          have hs := Nat.find_spec (hex h)
          rwa [hfind] at hs
        have hginf : g h = ∞ := hspec
        exact ⟨hφ₀Γ h, by simp [hginf]⟩
      · -- band m: select below the upper edge, bound below by the lower edge
        have hspec : bandPred ε' (m + 1) (g h) := by
          have hs := Nat.find_spec (hex h)
          rwa [hfind] at hs
        have hlt : g h < ((m + 1 : ℕ) : ℝ≥0∞) * ε' := hspec
        obtain ⟨e, heΓ, heF⟩ := iInf_fiber_lt hlt
        have hsel := hχsel (m + 1) h ⟨e, heΓ, heF⟩
        have hlow : ((m : ℕ) : ℝ≥0∞) * ε' ≤ g h :=
          band_lower_bound fun j hj =>
            Nat.find_min (hex h) (by rw [hfind]; exact hj)
        refine ⟨hsel.1, ?_⟩
        calc F (h, χ (m + 1) h)
            ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ε' := le_of_lt hsel.2
          _ = ((m : ℕ) : ℝ≥0∞) * ε' + ε' := by push_cast; ring
          _ ≤ g h + ε' := add_le_add hlow le_rfl
    exact ⟨fun h => ψ (Nat.find (hex h)) h,
      AnalyticallyMeasurable.find hψmeas hp hex,
      fun h => (hcorrect h).1,
      fun h => le_trans (hcorrect h).2 (add_le_add le_rfl hε'ε)⟩
