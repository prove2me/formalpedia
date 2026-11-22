-- Prove2me | solution 1 for pac_not_implies_online
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:22.921411+00:00
-- url     : https://prove2.me/submissions/903d7f07-5343-4166-be64-da6c2aa647a3

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
public import Theorems.Thm_P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4
public import Theorems.Thm_forward_direction

section
@[expose] public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
section ClassicalInstances
attribute [local instance] Classical.propDecidable
end ClassicalInstances
private theorem threshold_not_shatter_pair {S : Finset ℕ} (hcard : 2 ≤ S.card) :
    ¬ Shatters ℕ thresholdClass S := by
  intro hshat
  -- Extract two distinct elements from S
  have ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  -- Threshold monotonicity: (· ≤ n) with n < a implies n < b for a < b
  -- So no threshold can map a ↦ false and b ↦ true when a < b
  -- (and symmetrically for b < a).
  -- We show: for EVERY concept c ∈ thresholdClass, if c(a) = false then c(b) = false
  -- (regardless of ordering of a,b — but we'll use that they're distinct)
  -- Actually, we need the SPECIFIC labeling where the smaller gets false.
  -- Since we don't know who's smaller, we use that threshold monotonicity gives:
  -- ∀ n, ∀ x y, x ≤ y → decide(y ≤ n) = true → decide(x ≤ n) = true
  -- Equivalently: decide(x ≤ n) = false → decide(y ≤ n) = false when x ≤ y
  -- So: labeling (a ↦ false, b ↦ true) impossible when a < b
  --     labeling (b ↦ false, a ↦ true) impossible when b < a
  -- Both impossible since a ≠ b. Pick whichever gives a contradiction.
  -- We prove: ∀ c = (· ≤ n), ¬(c a = false ∧ c b = true) ∧ ¬(c b = false ∧ c a = true)
  -- Then ANY labeling that distinguishes a and b is unrealizable. But shattering
  -- requires ALL labelings, so there's a labeling distinguishing a and b.
  -- Pick the labeling that assigns a ↦ false and b ↦ true:
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · -- a < b: labeling (a ↦ false, b ↦ true) is impossible for monotone thresholds
    obtain ⟨c, ⟨n, rfl⟩, hc⟩ := hshat (fun s =>
      if (s : ℕ) = a then false else true)
    have h1 := hc ⟨a, ha⟩
    have h2 := hc ⟨b, hb⟩
    -- h1 : decide (a ≤ n) = if a = a then false else true
    -- h2 : decide (b ≤ n) = if b = a then false else true
    -- Manually reduce the if-then-else
    have : (⟨a, ha⟩ : ↥S).val = a := rfl
    have : (⟨b, hb⟩ : ↥S).val = b := rfl
    -- The coercion from ↥S to ℕ gives a (resp. b), so the condition is a = a (resp. b = a)
    have hca : decide (a ≤ n) = false := by
      convert h1 using 1; simp
    have hcb : decide (b ≤ n) = true := by
      convert h2 using 1
      simp only [show (b : ℕ) ≠ a from Ne.symm hab, ite_false]
    simp only [decide_eq_false_iff_not, not_le] at hca
    simp only [decide_eq_true_eq] at hcb
    omega
  · -- b < a: labeling (b ↦ false, a ↦ true) is impossible
    obtain ⟨c, ⟨n, rfl⟩, hc⟩ := hshat (fun s =>
      if (s : ℕ) = b then false else true)
    have hcb : decide (b ≤ n) = false := by
      convert hc ⟨b, hb⟩ using 1; simp
    have hca : decide (a ≤ n) = true := by
      simp_all
    simp only [decide_eq_false_iff_not, not_le] at hcb
    simp only [decide_eq_true_eq] at hca
    omega
private theorem vcdim_threshold_finite : VCDim ℕ thresholdClass < ⊤ := by
  -- Show VCDim ≤ 1 < ⊤
  apply lt_of_le_of_lt _ (WithTop.coe_lt_top (a := 1))
  -- VCDim = ⨆ S shattered, S.card. Need all shattered S to have card ≤ 1.
  apply iSup₂_le
  intro S hshat
  by_contra hgt
  push Not at hgt
  have hcard2 : 2 ≤ S.card := by
    exact_mod_cast hgt
  exact threshold_not_shatter_pair hcard2 hshat
private theorem thresholdTree_shattered (lo : ℕ) (d : ℕ)
    (C : ConceptClass ℕ Bool)
    (hC : ∀ n, lo ≤ n → n < lo + 2 ^ d → (fun x => decide (x ≤ n)) ∈ C) :
    (thresholdTree lo d).isShattered C := by
  induction d generalizing lo C with
  | zero =>
    -- Depth 0: need C.Nonempty. lo ≤ lo < lo + 1 = lo + 2^0
    exact ⟨_, hC lo le_rfl (by simp)⟩
  | succ d ih =>
    simp only [thresholdTree, LTree.isShattered]
    set mid := lo + 2 ^ d with hmid_def
    have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    have hpow_succ : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ∃ c ∈ C, c mid = true: take threshold n = mid
      refine ⟨_, hC mid (Nat.le_add_right lo _) ?_, by simp⟩
      rw [hpow_succ]; omega
    · -- ∃ c ∈ C, c mid = false: take threshold n = mid - 1
      have hmid_pos : 0 < mid := by omega
      refine ⟨_, hC (mid - 1) (by omega) (by rw [hpow_succ]; omega), ?_⟩
      simp only [decide_eq_false_iff_not, not_le]; omega
    · -- Left subtree: thresholdTree mid d, shattered by {c ∈ C | c mid = true}
      apply ih mid {c ∈ C | c mid = true}
      intro n hn1 hn2
      constructor
      · exact hC n (by omega) (by rw [hpow_succ]; omega)
      · simp [decide_eq_true_eq]; omega
    · -- Right subtree: thresholdTree lo d, shattered by {c ∈ C | c mid = false}
      apply ih lo {c ∈ C | c mid = false}
      intro n hn1 hn2
      constructor
      · exact hC n hn1 (lt_of_lt_of_le hn2 (by rw [hpow_succ]; omega))
      · simp [decide_eq_false_iff_not, not_le]; omega
private theorem threshold_shattered_all_depths :
    ∀ d : ℕ, ∃ T : LTree ℕ d, T.isShattered thresholdClass :=
  fun d => ⟨thresholdTree 0 d, thresholdTree_shattered 0 d thresholdClass
    (fun n _ _ => ⟨n, rfl⟩)⟩
private theorem ldim_threshold_top : LittlestoneDim ℕ thresholdClass = ⊤ := by
  -- In WithBot (WithTop ℕ), ⊤ = ↑(⊤ : WithTop ℕ)
  -- Show: for all d, LittlestoneDim ≥ ↑↑d. Then LittlestoneDim = ⊤.
  by_contra hne
  push Not at hne
  have hlt : LittlestoneDim ℕ thresholdClass < ⊤ := lt_top_iff_ne_top.mpr hne
  -- Extract finite bound
  cases hc : LittlestoneDim ℕ thresholdClass with
  | bot =>
    -- ⊥ means empty class, but thresholdClass is nonempty
    have hne : thresholdClass.Nonempty := ⟨_, 0, rfl⟩
    have hge : LittlestoneDim ℕ thresholdClass ≥ ↑(↑0 : WithTop ℕ) :=
      le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
    rw [hc] at hge; exact absurd hge (by simp)
  | coe v =>
    cases v with
    | top => rw [hc] at hlt; exact absurd hlt (lt_irrefl _)
    | coe n =>
      -- LittlestoneDim = ↑↑n, but we can shatter depth n+1
      have ⟨T, hT⟩ := threshold_shattered_all_depths (n + 1)
      have hge : LittlestoneDim ℕ thresholdClass ≥ ↑(↑(n + 1) : WithTop ℕ) :=
        le_iSup₂_of_le (n + 1) ⟨T, hT⟩ le_rfl
      rw [hc] at hge
      exact absurd hge (by
        simp only [WithBot.coe_le_coe]
        exact not_le.mpr (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)))
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
theorem _root_.solution :
    ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      PACLearnable X C ∧ ¬ OnlineLearnable X Bool C := by
  refine ⟨ℕ, ⊤, thresholdClass, ?_, ?_⟩
  · -- PAC learnable: VCDim < ⊤ → PACLearnable (via UC route)
    have hWB : @WellBehavedVC ℕ ⊤ thresholdClass := by
      intro D _ c m ε
      have hmeas_singleton_pi : ∀ (f : Fin m → ℕ),
          @MeasurableSet _ (@MeasurableSpace.pi (Fin m) (fun _ => ℕ) (fun _ => ⊤)) {f} := by
        simp_all
      have hprod_top : (inferInstance : MeasurableSpace ((Fin m → ℕ) × (Fin m → ℕ))) = ⊤ := by
        apply le_antisymm le_top
        intro s _
        have hs_union : s = ⋃ p ∈ s, {p} := by ext p; simp
        rw [hs_union]
        apply MeasurableSet.biUnion (Set.to_countable s)
        intro ⟨a, b⟩ _
        have : ({(a, b)} : Set ((Fin m → ℕ) × (Fin m → ℕ))) = {a} ×ˢ {b} := by
          ext ⟨x, y⟩; simp [Prod.mk.injEq]
        rw [this]
        exact (hmeas_singleton_pi a).prod (hmeas_singleton_pi b)
      have hmeas_all : ∀ s : Set ((Fin m → ℕ) × (Fin m → ℕ)),
          @MeasurableSet _ (inferInstance : MeasurableSpace ((Fin m → ℕ) × (Fin m → ℕ))) s := by
        intro s; rw [hprod_top]; exact MeasurableSpace.measurableSet_top
      exact (hmeas_all _).nullMeasurableSet
    exact vcdim_finite_imp_pac_via_uc' ℕ thresholdClass vcdim_threshold_finite
      (fun _ _ _ _ => MeasurableSpace.measurableSet_top)
      (fun _ _ _ => MeasurableSpace.measurableSet_top)
      hWB
  · -- ¬ OnlineLearnable: LittlestoneDim = ⊤ → ¬ OnlineLearnable
    intro hol
    have hfin := forward_direction ℕ thresholdClass hol
    rw [ldim_threshold_top] at hfin
    exact lt_irrefl _ hfin
