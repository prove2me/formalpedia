-- Prove2me | solution 1 for uc_does_not_imply_online
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:42.720043+00:00
-- url     : https://prove2.me/submissions/ad0ac748-721c-4bed-8c12-1a4e095552aa

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_P2M_vcdim_finite_imp_uc__685a2436ce92

section
@[expose] public section
universe u
attribute [local instance] Classical.propDecidable
section UCNotOnline
private theorem thresholdX_not_shatter_pair {X : Type u} {φ : ℕ ↪ X}
    {S : Finset X} (hcard : 2 ≤ S.card) :
    ¬ Shatters X (thresholdClassX φ) S := by
  intro hshat
  have ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨c₁, ⟨n₁, rfl⟩, hc₁⟩ := hshat (fun s => if (s : X) = a then true else false)
  have hc₁a : ∃ k, k ≤ n₁ ∧ φ k = a := by
    simpa using hc₁ ⟨a, ha⟩
  have hc₁b : ¬ ∃ k, k ≤ n₁ ∧ φ k = b := by
    intro hbad
    simp_all
  obtain ⟨c₂, ⟨n₂, rfl⟩, hc₂⟩ := hshat (fun s => if (s : X) = b then true else false)
  have hc₂a : ¬ ∃ k, k ≤ n₂ ∧ φ k = a := by
    simp_all
  have hc₂b : ∃ k, k ≤ n₂ ∧ φ k = b := by
    simpa using hc₂ ⟨b, hb⟩
  obtain ⟨i, hi_le, rfl⟩ := hc₁a
  obtain ⟨j, hj_le, hφj⟩ := hc₂b
  have hj_gt : n₁ < j := by
    by_contra h; simp_all
  have hi_gt : n₂ < i := by
    simp_all
  omega
private theorem vcdim_thresholdX_finite {X : Type u} (φ : ℕ ↪ X) :
    VCDim X (thresholdClassX φ) < ⊤ := by
  apply lt_of_le_of_lt _ (WithTop.coe_lt_top (a := 1))
  apply iSup₂_le
  intro S hshat
  by_contra hgt
  push Not at hgt
  have hcard2 : 2 ≤ S.card := by exact_mod_cast hgt
  exact thresholdX_not_shatter_pair hcard2 hshat
private theorem mistakesFromG_init_eq {X : Type u}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    mistakesFromG L L.init c seq = L.mistakes c seq := by
  suffices h : ∀ s : L.State, mistakesFromG L s c seq = L.mistakesFrom s c seq by
    simpa [OnlineLearner.mistakes] using h L.init
  induction seq with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    simp [mistakesFromG, OnlineLearner.mistakesFrom, ih]
private theorem adversary_threshold {X : Type u} {φ : ℕ ↪ X}
    (L : OnlineLearner X Bool) (s : L.State) (lo : ℕ) :
    ∀ d : ℕ, ∃ (seq : List X) (n : ℕ),
      lo ≤ n ∧ n < lo + 2 ^ d ∧
      (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) ∈ thresholdClassX φ ∧
      mistakesFromG L s (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) seq = d := by
  intro d
  induction d generalizing lo s with
  | zero =>
    refine ⟨[], lo, le_rfl, by simp, ⟨lo, rfl⟩, rfl⟩
  | succ d ih =>
    set mid := lo + 2 ^ d with hmid_def
    have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    by_cases hpred : L.predict s (φ mid) = true
    · obtain ⟨seq', n, hn_lo, hn_hi, hn_mem, hn_count⟩ := ih (L.update s (φ mid) false) lo
      have hn_lt_mid : n < mid := by omega
      have hcn_mid : decide (∃ k, k ≤ n ∧ φ k = φ mid) = false := by
        simp_all
      refine ⟨φ mid :: seq', n, hn_lo, by ring_nf; omega, hn_mem, ?_⟩
      change (if L.predict s (φ mid) ≠ _ then 1 else 0) +
        mistakesFromG L (L.update s (φ mid) _) _ seq' = d + 1
      have : (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) (φ mid) = false := hcn_mid
      rw [this, hpred]; simp; omega
    · have hpf : L.predict s (φ mid) = false := by
        cases h : L.predict s (φ mid) <;> simp_all
      obtain ⟨seq', n, hn_lo, hn_hi, hn_mem, hn_count⟩ := ih (L.update s (φ mid) true) mid
      have hn_ge_mid : mid ≤ n := hn_lo
      have hcn_mid : decide (∃ k, k ≤ n ∧ φ k = φ mid) = true := by
        simp only [decide_eq_true_eq]; exact ⟨mid, hn_ge_mid, rfl⟩
      refine ⟨φ mid :: seq', n, by omega, by ring_nf; omega, hn_mem, ?_⟩
      change (if L.predict s (φ mid) ≠ _ then 1 else 0) +
        mistakesFromG L (L.update s (φ mid) _) _ seq' = d + 1
      have : (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) (φ mid) = true := hcn_mid
      rw [this, hpf]; simp; omega
end UCNotOnline
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X] [Infinite X]
    (hmeas_C_all : ∀ (C : ConceptClass X Bool), ∀ h ∈ C, Measurable h)
    (hc_meas_all : ∀ c : Concept X Bool, Measurable c)
    (hWB_all : ∀ (C : ConceptClass X Bool), WellBehavedVC X C) :
    ¬ (∀ (C : ConceptClass X Bool),
      HasUniformConvergence X C →
        ∃ (M : ℕ), MistakeBounded X Bool C M) := by
  intro h
  have φ := Infinite.natEmbedding X
  set C := thresholdClassX φ with hC_def
  have hUC : HasUniformConvergence X C :=
    vcdim_finite_imp_uc' X C (vcdim_thresholdX_finite φ) (hmeas_C_all C) hc_meas_all (hWB_all C)
  obtain ⟨M, L, hL⟩ := h C hUC
  obtain ⟨seq, n, _, _, hn_mem, hcount⟩ :=
    adversary_threshold L L.init 0 (M + 1)
  have hbound := hL _ hn_mem seq
  rw [← mistakesFromG_init_eq] at hbound
  omega
