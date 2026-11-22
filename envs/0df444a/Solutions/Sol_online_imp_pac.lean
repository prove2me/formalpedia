-- Prove2me | solution 1 for online_imp_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:30.41791+00:00
-- url     : https://prove2.me/submissions/e837bef5-ee70-4e66-98d3-a366f04f8786

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Extended
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Separation
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas
public import Theorems.Thm_P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4

section
@[expose] public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
private theorem mistakesFromU_init_eq {X : Type u}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    mistakesFromU L L.init c seq = L.mistakes c seq := by
  suffices h : ∀ s : L.State, mistakesFromU L s c seq = L.mistakesFrom s c seq by
    simpa [OnlineLearner.mistakes] using h L.init
  induction seq with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    simp [mistakesFromU, OnlineLearner.mistakesFrom, ih]
private theorem shatters_restrict {X : Type u} [DecidableEq X] {C : ConceptClass X Bool}
    {S : Finset X} (hshat : Shatters X C S) {x : X} (hx : x ∈ S) (b : Bool) :
    Shatters X {c ∈ C | c x = b} (S.erase x) := by
  classical
  intro f
  -- Build labeling on S: assign x ↦ b, everything else per f
  let f' : ↥S → Bool := fun ⟨y, hy⟩ =>
    if h : y ∈ S.erase x then f ⟨y, h⟩ else b
  obtain ⟨c, hcC, hc⟩ := hshat f'
  have hcx : c x = b := by
    simpa only [f', Finset.mem_erase, ne_eq, not_true_eq_false, false_and, dite_false]
      using hc ⟨x, hx⟩
  refine ⟨c, ⟨hcC, hcx⟩, fun ⟨y, hy⟩ => ?_⟩
  have hy_S : y ∈ S := Finset.mem_of_mem_erase hy
  simpa only [f', hy, dite_true] using hc ⟨y, hy_S⟩
private theorem adversary_from_shatters {X : Type u}
    (L : OnlineLearner X Bool) (s : L.State)
    {C : ConceptClass X Bool} {S : Finset X}
    (hshat : Shatters X C S) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧
      mistakesFromU L s c seq = S.card := by
  classical
  induction S using Finset.induction_on generalizing C s with
  | empty =>
    obtain ⟨c₀, hc₀, _⟩ := hshat (fun ⟨_, h⟩ => by simp at h)
    exact ⟨[], c₀, hc₀, rfl⟩
  | @insert x S' hx ih =>
    -- Present x to L. Choose label that causes a mistake.
    by_cases hpred : L.predict s x = true
    · -- L predicts true → assign false
      have hshat' := shatters_restrict hshat (Finset.mem_insert_self x S') false
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hcount⟩ :=
        ih (s := L.update s x false) hshat'
      refine ⟨x :: seq', c', hc'mem.1, ?_⟩
      simp only [mistakesFromU, hc'mem.2, hpred, Finset.card_insert_of_notMem hx]
      simp [hcount]; omega
    · -- L predicts false → assign true
      have hpf : L.predict s x = false := by
        cases h : L.predict s x <;> simp_all
      have hshat' := shatters_restrict hshat (Finset.mem_insert_self x S') true
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hcount⟩ :=
        ih (s := L.update s x true) hshat'
      refine ⟨x :: seq', c', hc'mem.1, ?_⟩
      simp only [mistakesFromU, hc'mem.2, hpf, Finset.card_insert_of_notMem hx]
      simp [hcount]; omega
private theorem vcdim_le_of_mistake_bounded {X : Type u}
    {C : ConceptClass X Bool} {M : ℕ}
    (hM : MistakeBounded X Bool C M) : VCDim X C ≤ ↑M := by
  apply iSup₂_le
  intro S hshat
  by_contra hgt
  push Not at hgt
  have hcard : M + 1 ≤ S.card := by exact_mod_cast WithTop.coe_lt_coe.mp hgt
  obtain ⟨L, hL⟩ := hM
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_from_shatters L L.init hshat
  have hbound := hL c hcC seq
  rw [← mistakesFromU_init_eq] at hbound
  omega
section ClassicalInstances
attribute [local instance] Classical.propDecidable
end ClassicalInstances
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hol : OnlineLearnable X Bool C)
    [MeasurableConceptClass X C] :
    PACLearnable X C := by
  have hmeas_C := MeasurableConceptClass.hmeas_C C
  have hc_meas := MeasurableConceptClass.hc_meas C
  have hWB := MeasurableConceptClass.hWB C
  -- Step 1: OnlineLearnable gives mistake bound M
  obtain ⟨M, hM⟩ := hol
  -- Step 2: VCDim ≤ M < ⊤
  have hvcdim : VCDim X C < ⊤ := by
    calc VCDim X C ≤ ↑M := vcdim_le_of_mistake_bounded hM
      _ < ⊤ := WithTop.coe_lt_top M
  -- Step 3: VCDim < ⊤ → PACLearnable (via UC route, no bad_consistent_covering)
  exact vcdim_finite_imp_pac_via_uc' X C hvcdim hmeas_C hc_meas hWB
