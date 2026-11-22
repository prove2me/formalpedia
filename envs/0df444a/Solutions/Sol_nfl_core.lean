-- Prove2me | solution 1 for nfl_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:41.224645+00:00
-- url     : https://prove2.me/submissions/93285d29-e8a8-405a-b96f-7a0fae02e301

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Theorems.Thm_uniformMeasure_isProbability

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    -- There exists a hard distribution and concept
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        -- The learner fails with positive probability
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1 / 8) }
          > 0 := by
  -- Step 1: Construct D = uniformMeasure X
  have hpos : 0 < Fintype.card X := by omega
  have hne : Nonempty X := Fintype.card_pos_iff.mp hpos
  let D := uniformMeasure X hne
  -- Step 2: D is a probability measure
  have hprob : MeasureTheory.IsProbabilityMeasure D :=
    uniformMeasure_isProbability X hne hpos
  refine ⟨D, hprob, ?_⟩
  -- PROOF (H₆ — per-sample counting + product measure positivity):
  -- (A) For ANY fixed xs, counting over c : X → Bool via pairing argument:
  --     ∃ c₀ with D{x | h(x) ≠ c₀(x)} > 1 / 8.
  -- (B) For c₀: {xs | error > 1 / 8} ∋ xs₀, so nonempty.
  -- (C) Product of uniform → every point has positive mass → set has pos measure.
  --
  -- The per-sample counting argument (pairing):
  -- For x ∉ range(xs), pair c with c' = Function.update c x (!c x).
  -- Same labeled sample → same h. Exactly one of (c, c') has h(x) ≠ c(x).
  -- So ∑_c #{disagree} ≥ (n-m) · 2^(n-1). Average ≥ (n-m)/2 ≥ n/4 > n/8.
  -- Pigeonhole: ∃ c₀ with errCount > n/8, hence D{error} > 1 / 8.
  --
  classical
  let xs₀ : Fin m → X := fun _ => hne.some
  -- The per-sample counting lemma: for any xs, ∃ c with error > 1 / 8
  have per_sample : ∀ (xs : Fin m → X), ∃ (c : X → Bool),
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
        > ENNReal.ofReal (1 / 8) := by
    intro xs
    -- ADVERSARIAL CONSTRUCTION: c = false on seen, !h on unseen.
    -- Same training data -> same h. Error >= D(unseen) >= 1 / 2 > 1 / 8.
    let h0 := L.learn (m := m) (fun i => (xs i, false))
    let c1 : X -> Bool := fun x => if x ∈ Set.range xs then false else !h0 x
    have hc1_train : (fun i => (xs i, c1 (xs i))) = fun i => (xs i, false) := by
      funext i; simp only [c1, Set.mem_range_self, ↓reduceIte]
    refine ⟨c1, ?_⟩; rw [hc1_train]
    -- Error set ⊇ unseen. For unseen x: c1(x) = !h0(x) ≠ h0(x).
    have herr_sup : (Set.range xs)ᶜ ⊆ {x : X | h0 x ≠ c1 x} := by
      intro x hx; simp only [Set.mem_compl_iff] at hx
      simp only [Set.mem_ofPred_eq, c1, if_neg hx]; cases h0 x <;> simp
    -- D(error) >= D(unseen) by monotonicity
    apply lt_of_lt_of_le _ (MeasureTheory.measure_mono herr_sup)
    -- D(unseen) = 1 - D(seen). D(seen) <= m/n <= 1 / 2. So D(unseen) >= 1 / 2 > 1 / 8.
    have hfin := Set.finite_range xs
    rw [show D (Set.range xs)ᶜ =
        1 - D (Set.range xs) from MeasureTheory.prob_compl_eq_one_sub hfin.measurableSet]
    -- Bound D(range xs) <= 1 / 2
    have hD_seen_le : D (Set.range xs) ≤ 1 / 2 := by
      change uniformMeasure X hne _ ≤ _
      unfold uniformMeasure
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul,
          MeasureTheory.Measure.count_apply_finite' hfin hfin.measurableSet]
      have hrc : hfin.toFinset.card ≤ m := by
        calc hfin.toFinset.card
            ≤ (Finset.image xs Finset.univ).card :=
              Finset.card_le_card (fun x hx => by
                simp_all)
          _ ≤ Fintype.card (Fin m) := Finset.card_image_le
          _ = m := Fintype.card_fin m
      have hn0 : (Fintype.card X : ENNReal) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
      calc (1 / (↑(Fintype.card X) : ENNReal)) * ↑hfin.toFinset.card
          ≤ (1 / ↑(Fintype.card X)) * (↑m : ENNReal) :=
            mul_le_mul_right (Nat.cast_le.mpr hrc) _
        _ ≤ 1 / 2 := by
            rw [one_div, one_div,
                ENNReal.inv_mul_le_iff hn0 (ENNReal.natCast_ne_top _),
                show (↑(Fintype.card X) : ENNReal) * (2 : ENNReal)⁻¹ =
                (↑(Fintype.card X) : ENNReal) / 2 from div_eq_mul_inv _ _ |>.symm,
                ENNReal.le_div_iff_mul_le
                  (Or.inl (two_ne_zero))
                  (Or.inl (ENNReal.ofNat_ne_top))]
            calc (↑m : ENNReal) * 2 = ↑(2 * m) := by push_cast; ring
              _ ≤ ↑(Fintype.card X) := Nat.cast_le.mpr hm
    -- 1 / 8 < 1 - D(seen) since D(seen) <= 1 / 2
    have h18 : ENNReal.ofReal (1 / 8) < 1 / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]; norm_num
    calc ENNReal.ofReal (1 / 8) < 1 / 2 := h18
      _ ≤ 1 - D (Set.range xs) := by
        -- 1 / 2 ≤ 1 - D(seen) since D(seen) ≤ 1 / 2 in ENNReal
        -- D(seen) ≤ 1 / 2 ≤ 1, so 1 - 1 / 2 ≤ 1 - D(seen)
        calc (1 : ENNReal) / 2 = 1 - 1 / 2 := by norm_num
          _ ≤ 1 - D (Set.range xs) := tsub_le_tsub_left hD_seen_le 1
  -- Apply to xs₀
  obtain ⟨c₀, hc₀⟩ := per_sample xs₀
  refine ⟨c₀, ?_⟩
  -- {xs | error > 1 / 8} ⊇ {xs₀}, so has positive product measure.
  -- Product of uniform D: every singleton has mass (1/|X|)^m > 0.
  -- Monotonicity: measure of superset ≥ measure of subset
  calc (0 : ENNReal)
      < MeasureTheory.Measure.pi (fun _ : Fin m => D) {xs₀} := by
        -- Use pi_singleton: pi μ {f} = ∏ i, μ i {f i}
        -- Need SigmaFinite for each factor. D is a probability measure, hence finite.
        have : ∀ i : Fin m, MeasureTheory.SigmaFinite ((fun _ => D) i) :=
          fun _ => @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ D inferInstance
        rw [MeasureTheory.Measure.pi_singleton]
        apply pos_iff_ne_zero.mpr
        rw [Finset.prod_ne_zero_iff]
        intro i _
        -- D {xs₀ i} ≠ 0: uniformMeasure gives mass 1/|X| > 0 to every singleton
        change D {xs₀ i} ≠ 0
        change (uniformMeasure X hne) {xs₀ i} ≠ 0
        simp only [uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
        simp_all
    _ ≤ MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs | D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            > ENNReal.ofReal (1 / 8) } := by
        apply MeasureTheory.measure_mono
        exact Set.singleton_subset_iff.mpr hc₀
