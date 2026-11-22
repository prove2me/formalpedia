-- Prove2me | solution 1 for universal_imp_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:29.114035+00:00
-- url     : https://prove2.me/submissions/abfdc8ed-ae0e-447e-9f9d-93be5bd0c05f

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
public import Theorems.Thm_MeasurableConceptClass_hc_meas
public import Theorems.Thm_block_extract_measurable
public import Theorems.Thm_iIndepFun_block_extract

section
@[expose] public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
private lemma learn_measurable_fixed
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  exact (hL_meas m).comp (measurable_const.prodMk measurable_id)
private lemma measurableSet_goodBlock_A
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (n : ℕ) :
    MeasurableSet
      { xs : Fin n → X |
          D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
            ≤ ENNReal.ofReal (rate n) } := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  have h_label : Measurable (fun p : (Fin n → X) × X =>
      fun i : Fin n => (p.1 i, c (p.1 i))) :=
    measurable_pi_iff.mpr (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (hc_meas.comp ((measurable_pi_apply i).comp measurable_fst)))
  have h_joint : Measurable (fun p : (Fin n → X) × X =>
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2) :=
    (hL_meas n).comp (h_label.prodMk measurable_snd)
  have h_c_snd : Measurable (fun p : (Fin n → X) × X => c p.2) :=
    hc_meas.comp measurable_snd
  have h_disagree : MeasurableSet {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} :=
    (measurableSet_eq_fun h_joint h_c_snd).compl
  have h_sec_eq : ∀ xs : Fin n → X, Prod.mk xs ⁻¹' {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} =
      {x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x} := by
    intro xs; ext x; rfl
  have h_meas_fn : Measurable (fun xs : Fin n → X =>
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }) := by
    simpa only [h_sec_eq] using measurable_measure_prodMk_left (ν := D) h_disagree
  exact h_meas_fn measurableSet_Iic
private lemma goodBlockEvent_measurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (k n : ℕ) :
    ∀ j : Fin k, MeasurableSet (goodBlockEvent L D c rate k n j) := by
  intro j
  have hpre : goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => blockExtract k n ω j) ⁻¹'
        { xs : Fin n → X |
            D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal (rate n) } := by
    ext ω; rfl
  rw [hpre]
  exact measurableSet_preimage (block_extract_measurable k n j)
    (measurableSet_goodBlock_A L D c hc_meas rate n)
private lemma map_block_extract_eq_pi
    {X : Type u} [MeasurableSpace X]
    (k n : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] (j : Fin k) :
    (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D)).map
      (fun ω : Fin (k * n) → X => blockExtract k n ω j)
      =
    MeasureTheory.Measure.pi (fun _ : Fin n => D) := by
  open MeasureTheory MeasureTheory.Measure ProbabilityTheory Equiv in
  -- The currying MeasurableEquiv: Fin(k*n) → X  ≃ᵐ  Fin k → (Fin n → X)
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin n => X) finProdFinEquiv.symm
  set cur := MeasurableEquiv.curry (Fin k) (Fin n) X
  set e : (Fin (k * n) → X) ≃ᵐ (Fin k → Fin n → X) := pcl.trans cur
  -- blockExtract = e pointwise
  have he : ∀ ω, blockExtract k n ω j = e ω j := by
    intro ω; ext i
    simp only [blockExtract, e, MeasurableEquiv.trans_apply, pcl, cur]
    simp [MeasurableEquiv.piCongrLeft, piCongrLeft_apply, MeasurableEquiv.curry,
      Function.curry]
  set μ := Measure.pi (fun _ : Fin (k * n) => D)
  set D' : Fin k → Measure (Fin n → X) := fun _ => Measure.pi (fun _ : Fin n => D)
  -- μ.map pcl preserves measure
  have hpcl : MeasurePreserving pcl μ (Measure.pi (fun _ : Fin k × Fin n => D)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k × Fin n => D) finProdFinEquiv.symm
  -- (flat on Fin k × Fin n).map cur = nested product
  have hcur : (Measure.pi (fun _ : Fin k × Fin n => D)).map cur = Measure.pi D' := by
    have h1 : Measure.pi (fun _ : Fin k × Fin n => D) =
        infinitePi (fun _ : Fin k × Fin n => D) :=
      (infinitePi_eq_pi (μ := fun _ : Fin k × Fin n => D)).symm
    rw [h1]
    have h3 : D' = fun _ : Fin k => infinitePi (fun _ : Fin n => D) := by
      funext; exact (infinitePi_eq_pi (μ := fun _ : Fin n => D)).symm
    have h2 : Measure.pi D' = infinitePi D' :=
      (infinitePi_eq_pi (μ := D')).symm
    rw [h2, h3]
    exact infinitePi_map_curry (fun _ : Fin k => fun _ : Fin n => D)
  -- μ.map e = Measure.pi D'
  have hmap_e : μ.map e = Measure.pi D' := by
    have : (e : (Fin (k * n) → X) → (Fin k → Fin n → X)) = cur ∘ pcl := rfl
    rw [this, ← map_map cur.measurable pcl.measurable, hpcl.map_eq, hcur]
  -- Factor through e and project
  have hcomp : (fun ω => blockExtract k n ω j) = (fun f => f j) ∘ (e : (Fin (k * n) → X) → _) := by
    ext ω i; exact congrFun (he ω) i
  calc μ.map (fun ω => blockExtract k n ω j)
      = μ.map ((fun f => f j) ∘ (e : (Fin (k * n) → X) → _)) := by rw [hcomp]
    _ = (Measure.pi D').map (fun f => f j) := by
          rw [← map_map (measurable_pi_apply j) e.measurable, hmap_e]
    _ = D' j := (measurePreserving_eval D' j).map_eq
    _ = Measure.pi (fun _ : Fin n => D) := rfl
private lemma iIndepSet_goodBlockEvents
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (k n : ℕ) :
    ProbabilityTheory.iIndepSet
      (goodBlockEvent L D c rate k n)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D)) := by
  -- Step 1: Define A (good training set) and express goodBlockEvent as preimage
  let A : Set (Fin n → X) :=
    { xs : Fin n → X |
        D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
          ≤ ENNReal.ofReal (rate n) }
  have hA : MeasurableSet A := measurableSet_goodBlock_A L D c hc_meas rate n
  have hpre : ∀ j : Fin k, goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => blockExtract k n ω j) ⁻¹' A := by
    intro j; ext ω; rfl
  -- Step 2: Convert iIndepSet to iIndep, then bridge from iIndepFun
  rw [ProbabilityTheory.iIndepSet_iff_iIndep]
  apply ProbabilityTheory.iIndep_of_iIndep_of_le
      ((ProbabilityTheory.iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_block_extract k n D))
  -- Step 3: Show generateFrom {goodBlockEvent j} ≤ comap (blockExtract · j) _
  intro j
  apply MeasurableSpace.generateFrom_le
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs, hpre j]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩
private lemma goodBlockEvent_prob_ge_two_thirds
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L] (rate : ℕ → ℝ)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3))
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hcC : c ∈ C) (hc_meas : Measurable c)
    (k n : ℕ) (j : Fin k) :
    (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D))
      (goodBlockEvent L D c rate k n j)
      ≥ ENNReal.ofReal (2 / 3) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  -- Step 1: Express goodBlockEvent as preimage of the "good training set" A under blockExtract
  let A : Set (Fin n → X) :=
    { xs : Fin n → X |
        D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
          ≤ ENNReal.ofReal (rate n) }
  have hpre : goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => blockExtract k n ω j) ⁻¹' A := by
    ext ω; rfl
  -- Step 2: Push forward via map_block_extract_eq_pi
  have hA : MeasurableSet A := measurableSet_goodBlock_A L D c hc_meas rate n
  rw [hpre, ← MeasureTheory.Measure.map_apply (block_extract_measurable k n j) hA,
      map_block_extract_eq_pi k n D j]
  -- Step 3: Apply the base learner guarantee
  exact huniv D inferInstance c hcC n
section ClassicalInstances
attribute [local instance] Classical.propDecidable
private lemma chebyshev_seven_twelfths_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (h_delta_pos : 0 < δ)
    (hk : (36 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2 / 3)) :
    μ {ω | 7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ events j)).card} ≥
      ENNReal.ofReal (1 - δ) := by
  open MeasureTheory ProbabilityTheory Finset in
  -- Step 1: Define indicator random variables X_j and their sum S
  set X : Fin k → Ω → ℝ := fun j => (events j).indicator (fun _ => (1 : ℝ))
  set S : Ω → ℝ := fun ω => ∑ j : Fin k, X j ω
  -- Step 2: S counts the number of events that hold
  have hS_count : ∀ ω, S ω = ((univ.filter (fun j => ω ∈ events j)).card : ℝ) := by
    intro ω; simp only [S, X, Set.indicator_apply]
    simp_all
  -- Step 3: The indicator functions are independent
  have hindep_fun : iIndepFun (m := fun _ => inferInstance)
      (fun j => (events j).indicator (fun _ => (1 : ℝ))) μ :=
    hindep.iIndepFun_indicator
  -- Step 4: Each X_j is bounded in [0, 1], hence MemLp 2
  have hX_bound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro j; apply Filter.Eventually.of_forall; intro ω
    simp only [X, Set.indicator_apply, Set.mem_Icc]
    split_ifs <;> constructor <;> norm_num
  have hX_meas : ∀ j, AEMeasurable (X j) μ := by
    intro j
    exact (stronglyMeasurable_one.indicator (hevents_meas j)).aestronglyMeasurable.aemeasurable
  have hX_memLp : ∀ j, MemLp (X j) 2 μ := by
    intro j
    exact memLp_of_bounded (hX_bound j)
      (stronglyMeasurable_one.indicator (hevents_meas j)).aestronglyMeasurable 2
  -- Step 5: Variance of each X_j ≤ 1 / 4 (Popoviciu)
  have hvar_bound : ∀ j, ProbabilityTheory.variance (X j) μ ≤ 1 / 4 := by
    intro j
    calc ProbabilityTheory.variance (X j) μ
        ≤ ((1 - 0) / 2) ^ 2 := variance_le_sq_of_bounded (hX_bound j) (hX_meas j)
      _ = 1 / 4 := by norm_num
  -- Step 6: Pairwise independence for variance_sum
  have hpairwise : Set.Pairwise (↑(univ : Finset (Fin k)))
      (fun i j => (X i) ⟂ᵢ[μ] (X j)) := by
    intro i _ j _ hij; exact hindep_fun.indepFun hij
  -- Step 7: Variance of S = sum of variances ≤ k/4
  have hvar_S : ProbabilityTheory.variance (∑ j : Fin k, X j) μ ≤ k / 4 := by
    rw [IndepFun.variance_sum (fun i _ => hX_memLp i) hpairwise]
    calc ∑ j : Fin k, ProbabilityTheory.variance (X j) μ
        ≤ ∑ _j : Fin k, (1 : ℝ) / 4 := sum_le_sum (fun j _ => hvar_bound j)
      _ = k * (1 / 4) := by rw [sum_const]; simp [nsmul_eq_mul]
      _ = k / 4 := by ring
  -- Step 8: k > 0
  have hk_pos : (0 : ℝ) < ↑k := lt_of_lt_of_le (by positivity : (0 : ℝ) < 36 / δ) hk
  -- Step 9: E[X_j] ≥ 2 / 3
  have hEX : ∀ j, ∫ ω, X j ω ∂μ ≥ 2 / 3 := by
    intro j; simp only [X]
    rw [integral_indicator_const (1 : ℝ) (hevents_meas j), smul_eq_mul, mul_one]
    rw [ge_iff_le, ← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one)
      (hprob j).le
  -- Step 10: Integrability
  have hX_int : ∀ j, Integrable (X j) μ := fun j => (hX_memLp j).integrable one_le_two
  -- Step 11: E[S] ≥ 2k/3 (S = fun ω => ∑ j, X j ω)
  have hES : ∫ ω, S ω ∂μ ≥ 2 * ↑k / 3 := by
    change ∫ ω, (∑ j : Fin k, X j ω) ∂μ ≥ _
    rw [integral_finsetSum univ (fun j _ => hX_int j)]
    calc ∑ j : Fin k, ∫ ω, X j ω ∂μ
        ≥ ∑ _j : Fin k, (2 : ℝ) / 3 := sum_le_sum (fun j _ => hEX j)
      _ = ↑k * (2 / 3) := by rw [sum_const]; simp [nsmul_eq_mul]
      _ = 2 * ↑k / 3 := by ring
  -- Step 12: MemLp S 2 μ
  have hS_memLp : MemLp S 2 μ := by
    change MemLp (fun ω => ∑ j : Fin k, X j ω) 2 μ
    have h := memLp_finsetSum univ (fun j (_ : j ∈ univ) => hX_memLp j)
    convert h using 1
  -- Step 13: Var[S] ≤ k/4
  have hvar_S_fn : ProbabilityTheory.variance S μ ≤ ↑k / 4 := by
    change ProbabilityTheory.variance (fun ω => ∑ j : Fin k, X j ω) μ ≤ _
    have : ProbabilityTheory.variance (fun ω => ∑ j : Fin k, X j ω) μ =
        ProbabilityTheory.variance (∑ j : Fin k, X j) μ := by
      congr 1; ext ω; simp [Finset.sum_apply]
    rw [this]; exact hvar_S
  -- Step 14: Apply Chebyshev
  have hk12_pos : (0 : ℝ) < ↑k / 12 := by positivity
  have hcheb := meas_ge_le_variance_div_sq hS_memLp hk12_pos
  -- Step 15: Bound Var[S]/(k/12)^2 ≤ δ
  have hcheb_bound : ProbabilityTheory.variance S μ / ((↑k / 12) ^ 2) ≤ δ := by
    calc ProbabilityTheory.variance S μ / ((↑k / 12) ^ 2)
        ≤ (↑k / 4) / ((↑k / 12) ^ 2) :=
          div_le_div_of_nonneg_right hvar_S_fn (sq_nonneg _)
      _ = 36 / ↑k := by field_simp; ring
      _ ≤ δ := by
          rw [div_le_iff₀ hk_pos]
          have h36 : 36 / δ * δ = 36 := div_mul_cancel₀ 36 (ne_of_gt h_delta_pos)
          nlinarith [hk]
  -- Step 16: μ{bad} ≤ ofReal δ
  have hbad_le : μ {ω | ↑k / 12 ≤ |S ω - ∫ ω, S ω ∂μ|} ≤ ENNReal.ofReal δ :=
    le_trans hcheb (ENNReal.ofReal_le_ofReal hcheb_bound)
  -- Step 17: {S ≥ 7k/12}ᶜ ⊆ {bad}
  have hcompl_sub : {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ⊆
      {ω | ↑k / 12 ≤ |S ω - ∫ ω, S ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_ofPred_eq]
    have hgap : ∫ ω, S ω ∂μ - S ω ≥ ↑k / 12 := by linarith
    calc ↑k / 12 ≤ ∫ ω, S ω ∂μ - S ω := hgap
      _ ≤ |S ω - ∫ ω, S ω ∂μ| := by rw [abs_sub_comm]; exact le_abs_self _
  -- Step 18: μ{S ≥ 7k/12}ᶜ ≤ ofReal δ
  have hcompl_le : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ≤ ENNReal.ofReal δ :=
    le_trans (μ.mono hcompl_sub) hbad_le
  -- Step 19: Measurability
  have hS_meas : Measurable S := by
    change Measurable (fun ω => ∑ j : Fin k, X j ω)
    exact Finset.measurable_sum _ (fun j _ =>
      (stronglyMeasurable_one.indicator (hevents_meas j)).measurable)
  have hmeas : MeasurableSet {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} :=
    hS_meas measurableSet_Ici
  -- Step 20: μ{S ≥ 7k/12} ≥ 1 - δ
  have hgood : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} ≥ ENNReal.ofReal (1 - δ) := by
    rw [ge_iff_le, ENNReal.ofReal_sub _ h_delta_pos.le, ENNReal.ofReal_one,
      ← measure_univ (μ := μ), ← measure_add_measure_compl hmeas,
      tsub_le_iff_right]
    exact add_le_add (le_refl _) hcompl_le
  -- Step 21: Convert from {7k/12 ≤ S ω} to {7*k ≤ 12 * card}
  apply le_trans hgood
  apply μ.mono
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hS_count ω] at hω
  have : (7 : ℝ) * ↑k ≤ 12 * ↑(univ.filter (fun j => ω ∈ events j)).card := by
    linarith
  exact_mod_cast this
end ClassicalInstances
private lemma majority_error_le_seven_rate_of_good_fraction
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X)
    {k : ℕ} (hk_pos : 0 < k)
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : Fin k → Concept X Bool)
    (hhs_meas : ∀ j : Fin k, Measurable (hs j))
    (good : Finset (Fin k))
    (hgoodfrac : 7 * k ≤ 12 * good.card)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgooderr : ∀ j ∈ good, D {x : X | hs j x ≠ c x} ≤ ENNReal.ofReal ρ) :
    D {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
      ≤ ENNReal.ofReal (7 * ρ) := by
  classical
  let bad : Fin k → Set X := fun j => {x : X | hs j x ≠ c x}
  have hbad_meas : ∀ j, MeasurableSet (bad j) := by
    intro j
    change MeasurableSet {x : X | hs j x ≠ c x}
    have : {x : X | hs j x ≠ c x} = {x : X | hs j x = c x}ᶜ := by
      ext x; simp [ne_eq, Set.mem_compl_iff]
    rw [this]
    exact (measurableSet_eq_fun (hhs_meas j) hc_meas).compl
  let G : X → ENNReal := fun x =>
    ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
  have hG_meas : Measurable G := by
    refine Finset.measurable_sum good ?_
    intro j _
    exact Measurable.indicator measurable_const (hbad_meas j)
  have hG_ae : AEMeasurable G D := hG_meas.aemeasurable
  let threshold : ENNReal := (2 * good.card - k : ℕ)
  have hklt : k < 2 * good.card := by
    have : (7 : ℕ) * k ≤ 12 * good.card := hgoodfrac
    omega
  have hden_pos_nat : 0 < 2 * good.card - k := Nat.sub_pos_of_lt hklt
  have hmajority_sub :
      {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
        ⊆ {x : X | threshold ≤ G x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    set wrongAll : ℕ := (Finset.univ.filter (fun j => hs j x ≠ c x)).card with hwrongAll_def
    set wrongGood : ℕ := (good.filter (fun j => hs j x ≠ c x)).card with hwrongGood_def
    have hwrong_all : k ≤ 2 * wrongAll := by
      -- boosted_majority disagrees with c x means majority voted wrong
      have hfilt_id : (Finset.univ.filter (fun j : Fin k => hs j x)).card
          = (Finset.univ.filter (fun j : Fin k => hs j x = true)).card := by
        simp
      cases hcx : c x with
      | false =>
        have hmaj : boosted_majority k (fun j => hs j x) = true := by
          simp_all
        change decide (k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card) =
          true at hmaj
        have hmaj_lt : k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x = true)).card := by
          simp_all
        have hfilt_ne : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x))
            = (Finset.univ.filter (fun j : Fin k => hs j x = true)) := by
          ext j; simp [hcx]
        rw [hwrongAll_def, hfilt_ne]
        omega
      | true =>
        have hmaj : boosted_majority k (fun j => hs j x) = false := by
          simp_all
        change decide (k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card) =
          false at hmaj
        have hmaj_le : 2 * (Finset.univ.filter (fun j : Fin k => hs j x = true)).card ≤ k := by
          simp_all
        have hfilt_ne : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x))
            = (Finset.univ.filter (fun j : Fin k => hs j x = false)) := by
          ext j; simp [hcx]
        have hcomp2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
          (fun j => hs j x = true)
        simp only [Finset.card_univ, Fintype.card_fin] at hcomp2
        have hfilt_false : (Finset.univ.filter (fun j : Fin k => ¬hs j x = true)).card
            = (Finset.univ.filter (fun j : Fin k => hs j x = false)).card := by
          simp only [Bool.not_eq_true]
        rw [hwrongAll_def, hfilt_ne]
        omega
    have hwrong_split : wrongAll ≤ wrongGood + (k - good.card) := by
      -- Every wrong voter in univ is either in good or not in good
      -- wrongAll = #{j ∈ univ | wrong}, wrongGood = #{j ∈ good | wrong}
      -- #{j ∈ univ \ good | wrong} ≤ |univ \ good| = k - good.card
      have hgood_card_le : good.card ≤ k := by
        calc good.card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = k := Finset.card_fin k
      -- univ.filter p = (good.filter p) ∪ ((univ \ good).filter p)
      have hunion : Finset.univ.filter (fun j : Fin k => hs j x ≠ c x)
          = (good.filter (fun j => hs j x ≠ c x)) ∪
            ((Finset.univ \ good).filter (fun j => hs j x ≠ c x)) := by
        ext j
        simp [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hdisj : Disjoint (good.filter (fun j => hs j x ≠ c x))
          ((Finset.univ \ good).filter (fun j => hs j x ≠ c x)) := by
        apply Finset.disjoint_filter_filter
        exact disjoint_sdiff_self_right
      rw [hwrongAll_def, hunion, Finset.card_union_of_disjoint hdisj]
      have : ((Finset.univ \ good).filter (fun j : Fin k => hs j x ≠ c x)).card
          ≤ (Finset.univ \ good).card := Finset.card_filter_le _ _
      have hsdiff_card : (Finset.univ \ good).card = k - good.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        simp
      omega
    have hthreshold_nat : 2 * good.card - k ≤ 2 * wrongGood := by
      have h1 := hwrong_all
      have h2 := hwrong_split
      have h3 : good.card ≤ k := by
        calc good.card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = k := Finset.card_fin k
      omega
    change threshold ≤ G x
    suffices h : (2 * good.card - k : ℕ) ≤ 2 * wrongGood by
      change (↑(2 * good.card - k) : ENNReal) ≤
        ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
      have hsum_eq : ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
          = ↑(2 * wrongGood) := by
        simp only [bad, Set.indicator_apply, Set.mem_ofPred_eq]
        trans (∑ j ∈ good, if hs j x ≠ c x then (2 : ENNReal) else 0)
        · rfl
        have hcast : ∀ j ∈ good, (if hs j x ≠ c x then (2 : ENNReal) else 0)
            = (↑(if hs j x ≠ c x then 2 else 0 : ℕ) : ENNReal) := by
          intro j _; split <;> simp
        rw [Finset.sum_congr rfl hcast]
        push_cast [← Nat.cast_sum]
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul, mul_comm]
        rfl
      rw [hsum_eq]
      exact_mod_cast h
    exact hthreshold_nat
  have hG_int :
      ∫⁻ x, G x ∂D ≤ ENNReal.ofReal (2 * ↑good.card * ρ) := by
    have hsum_ae :
        ∀ j ∈ good,
          AEMeasurable ((bad j).indicator (fun _ => (2 : ENNReal))) D := by
      intro j _
      exact (Measurable.indicator measurable_const (hbad_meas j)).aemeasurable
    calc
      ∫⁻ x, G x ∂D
          = ∑ j ∈ good, ∫⁻ x, (bad j).indicator (fun _ => (2 : ENNReal)) x ∂D := by
              exact lintegral_finsetSum' good hsum_ae
      _ ≤ ∑ j ∈ good, ENNReal.ofReal (2 * ρ) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [lintegral_indicator_const (hbad_meas j)]
            calc (2 : ENNReal) * D (bad j)
                ≤ 2 * ENNReal.ofReal ρ := by gcongr; exact hgooderr j hj
              _ = ENNReal.ofReal (2 * ρ) := by
                    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = ↑good.card * ENNReal.ofReal (2 * ρ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ↑good.card * ρ) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
  have hthresh_ne_zero : threshold ≠ 0 := by
    change (↑(2 * good.card - k) : ENNReal) ≠ 0
    exact_mod_cast hden_pos_nat.ne'
  have hthresh_ne_top : threshold ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmarkov :
      D {x : X | threshold ≤ G x}
        ≤ (∫⁻ x, G x ∂D) / threshold :=
    meas_ge_le_lintegral_div hG_ae hthresh_ne_zero hthresh_ne_top
  have hratio :
      (∫⁻ x, G x ∂D) / threshold ≤ ENNReal.ofReal (7 * ρ) := by
    rw [ENNReal.div_le_iff hthresh_ne_zero hthresh_ne_top]
    calc ∫⁻ x, G x ∂D
          ≤ ENNReal.ofReal (2 * ↑good.card * ρ) := hG_int
      _ ≤ ENNReal.ofReal (7 * ρ) * threshold := by
            change ENNReal.ofReal (2 * ↑good.card * ρ)
              ≤ ENNReal.ofReal (7 * ρ) * (↑(2 * good.card - k) : ENNReal)
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have hgf : (7 : ℝ) * ↑k ≤ 12 * ↑good.card := by exact_mod_cast hgoodfrac
            have hcast : (↑(2 * good.card - k) : ℝ) = 2 * ↑good.card - ↑k := by
              rw [Nat.cast_sub (by omega : k ≤ 2 * good.card)]
              push_cast; ring
            rw [hcast]
            nlinarith
  calc
    D {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
        ≤ D {x : X | threshold ≤ G x} := D.mono hmajority_sub
    _ ≤ (∫⁻ x, G x ∂D) / threshold := hmarkov
    _ ≤ ENNReal.ofReal (7 * ρ) := hratio
private lemma boosted_sample_error_le_of_good_blocks
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X)
    (c : Concept X Bool) (hc_meas : Measurable c)
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (rate : ℕ → ℝ) (k n : ℕ)
    (ω : Fin (k * n) → X)
    (hk_pos : 0 < k)
    (hgoodfrac :
      7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)).card) :
    D {x : X |
        boosted_majority k
          (fun j => L.learn
            (fun i => (blockExtract k n ω j i, c (blockExtract k n ω j i))) x) ≠ c x}
      ≤ ENNReal.ofReal (7 * max (rate n) 0) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  classical
  let hs : Fin k → Concept X Bool := fun j =>
    L.learn (fun i => (blockExtract k n ω j i, c (blockExtract k n ω j i)))
  let good : Finset (Fin k) :=
    Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)
  have hhs_meas : ∀ j : Fin k, Measurable (hs j) := by
    intro j
    have : MeasurableBatchLearner X L := ⟨hL_meas⟩
    exact learn_measurable_fixed L
      (fun i => (blockExtract k n ω j i, c (blockExtract k n ω j i)))
  have hgooderr :
      ∀ j ∈ good, D {x : X | hs j x ≠ c x} ≤ ENNReal.ofReal (max (rate n) 0) := by
    intro j hj
    have hj' :
        D {x : X |
            L.learn (fun i => (blockExtract k n ω j i, c (blockExtract k n ω j i))) x ≠ c x}
          ≤ ENNReal.ofReal (rate n) := by
      simp only [good, Finset.mem_filter] at hj
      exact hj.2
    exact le_trans hj' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact majority_error_le_seven_rate_of_good_fraction
    (D := D) (k := k) hk_pos
    (c := c) (hc_meas := hc_meas)
    (hs := hs) (hhs_meas := hhs_meas)
    (good := good) (hgoodfrac := hgoodfrac)
    (ρ := max (rate n) 0) (hρ := le_max_right _ _)
    hgooderr
private theorem boost_two_thirds_to_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    [MeasurableHypotheses X C]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (rate : ℕ → ℝ)
    (hrate : ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3)) :
    PACLearnable X C := by
  have hc_meas : ∀ c ∈ C, Measurable c := MeasurableHypotheses.mem_measurable (C := C)
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  -- Step 1: Construct the boosted BatchLearner.
  -- L' splits m samples into k = Nat.sqrt(m)+1 blocks of size m/k,
  -- runs L on each block, and takes majority vote.
  let L' : BatchLearner X Bool := {
    hypotheses := Set.univ
    learn := fun {m} S x =>
      let k := Nat.sqrt m + 1
      let blk := m / k
      if blk = 0 then L.learn S x
      else
        boosted_majority k (fun j : Fin k =>
          L.learn (fun i : Fin blk => S ⟨j.val * blk + i.val, by
            have hj := j.isLt; have hi := i.isLt
            have hkblk : k * blk ≤ m := by
              rw [Nat.mul_comm]; exact Nat.div_mul_le_self m k
            calc j.val * blk + i.val
                < j.val * blk + blk := by omega
              _ = (j.val + 1) * blk := by ring
              _ ≤ k * blk := by exact Nat.mul_le_mul_right blk hj
              _ ≤ m := hkblk⟩) x)
    output_in_H := fun _ => Set.mem_univ _ }
  -- Step 2: Construct the sample complexity function.
  -- For given ε, δ > 0:
  --   kmin = ⌈36/δ⌉ + 2 (enough blocks for Chebyshev; ensures kmin ≥ 2)
  --   ε' = ε / 7 (rate target for majority error bound)
  --   m₀ = smallest n with rate(n) < ε'
  --   n = max m₀ (kmin - 1) (ensures n ≥ m₀ AND n+1 ≥ kmin)
  --   mf = (n+1) * n (= k * block_sz, with Nat.sqrt((n+1)*n) = n)
  refine ⟨L', fun ε δ =>
    if hε' : 0 < ε then
      if hδ' : 0 < δ then
        let kmin := Nat.ceil (36 / δ) + 2
        let ε' := ε / 7
        let m₀ := Nat.find (hrate ε' (by positivity))
        let n := max m₀ (kmin - 1)
        (n + 1) * n
      else 0
    else 0, ?_⟩
  -- Step 3: Prove the PAC bound.
  intro ε δ hε hδ D hD c hcC
  dsimp only
  rw [dif_pos hε, dif_pos hδ]
  have hε'_pos : 0 < ε / 7 := by positivity
  set kmin := Nat.ceil (36 / δ) + 2 with hkmin_def
  set n := max (Nat.find (hrate (ε / 7) hε'_pos)) (kmin - 1) with hn_def
  have hn_pos : 0 < n := by omega
  have hn1_pos : 0 < n + 1 := by omega
  have hsqrt : Nat.sqrt ((n + 1) * n) = n := by
    rw [show (n + 1) * n = n * n + n from by ring]
    exact Nat.sqrt_add_eq n (Nat.le_add_right n n)
  have hblk : (n + 1) * n / (n + 1) = n := Nat.mul_div_cancel_left n (by omega)
  have hblk_ne : ((n + 1) * n / (Nat.sqrt ((n + 1) * n) + 1)) ≠ 0 := by
    rw [hsqrt, hblk]; omega
  have hrate_n : rate n < ε / 7 := by
    exact Nat.find_spec (hrate (ε / 7) hε'_pos) n (le_max_left _ _)
  have h36k : (36 : ℝ) / δ ≤ ↑(n + 1) := by
    calc (36 : ℝ) / δ ≤ ↑(Nat.ceil (36 / δ)) := Nat.le_ceil _
      _ ≤ ↑kmin := by exact_mod_cast (by omega : Nat.ceil (36 / δ) ≤ kmin)
      _ ≤ ↑(n + 1) := by exact_mod_cast (by omega : kmin ≤ n + 1)
  -- Step 3b: Concentration instantiation
  have hevents_meas := goodBlockEvent_measurable L D c (hc_meas c hcC) rate (n + 1) n
  have hindep := iIndepSet_goodBlockEvents L D c (hc_meas c hcC) rate (n + 1) n
  have hprob := fun j => goodBlockEvent_prob_ge_two_thirds C L rate huniv D c hcC
    (hc_meas c hcC) (n + 1) n j
  have hconc := chebyshev_seven_twelfths_bound hδ h36k
    (goodBlockEvent L D c rate (n + 1) n) hevents_meas hindep hprob
  -- Step 3c: Rate bound
  have h7rate : 7 * max (rate n) 0 ≤ ε := by
    have : max (rate n) 0 ≤ ε / 7 := by
      rcases le_or_gt 0 (rate n) with h | h
      · simp [max_eq_left h]; linarith
      · rw [max_eq_right (le_of_lt h)]
        positivity
    linarith
  -- Step 3d: hlearn_unfold (P3c: congrArg ladder via boosted_majority cast)
  have hlearn_unfold : ∀ (ω : Fin ((n + 1) * n) → X) (x : X),
      L'.learn (fun i => (ω i, c (ω i))) x =
      boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (blockExtract (n + 1) n ω j i,
                           c (blockExtract (n + 1) n ω j i))) x) := by
    intro ω x
    simp only [L']
    have hblk_ne' : ¬ ((n + 1) * n / (((n + 1) * n).sqrt + 1) = 0) := hblk_ne
    rw [if_neg hblk_ne']
    have hsqrt' : ((n + 1) * n).sqrt + 1 = n + 1 := by rw [hsqrt]
    have hblk' : (n + 1) * n / (((n + 1) * n).sqrt + 1) = n := by rw [hsqrt]; exact hblk
    -- Prove by showing the boosted_majority applications are definitionally equal
    -- after casting the Fin types via the equalities hsqrt' and hblk'
    change boosted_majority _ _ = boosted_majority _ _
    -- Key: boosted_majority k f depends on k and Fin k.
    -- We show: boosted_majority k f = boosted_majority k' g when k = k' and f, g agree pointwise
    have hbm : ∀ {k k'} (hk : k = k') (f : Fin k → Bool) (g : Fin k' → Bool),
        (∀ j : Fin k, f j = g ⟨j, hk ▸ j.2⟩) → boosted_majority k f = boosted_majority k' g := by
      intros k k' hk f g hfg; subst hk; exact congrArg (boosted_majority k) (funext hfg)
    apply hbm hsqrt'
    intro j
    -- j : Fin(sqrt+1), need:
    --   L.learn (fun i:Fin(blk) => (ω ⟨j*blk+i, _⟩, c(...))) x
    -- = L.learn (fun i:Fin(n) => (blockExtract (n+1) n ω ⟨j, _⟩ i, c(...))) x
    -- Use the same helper pattern for the inner Fin cast
    -- Apply the same pattern for the inner Fin type cast (Fin blk → Fin n)
    -- We need: L.learn S₁ x = L.learn S₂ x where S₁ : Fin(blk) → ... and S₂ : Fin(n) → ...
    -- Use a helper that casts the learn input
    have hlearn_cast : ∀ {m m'} (hm : m = m') (S : Fin m → X × Bool) (S' : Fin m' → X × Bool),
        (∀ i : Fin m, S i = S' ⟨i, hm ▸ i.2⟩) → L.learn S x = L.learn S' x := by
      intros m m' hm S S' hS; subst hm; exact congrArg (L.learn · x) (funext hS)
    apply hlearn_cast hblk'
    intro ⟨i, hi⟩
    simp only [blockExtract, finProdFinEquiv, Equiv.coe_fn_mk, hblk']
    -- Goal: (ω ⟨j*n+i, _⟩, c (ω ⟨j*n+i, _⟩)) = (ω ⟨i+n*j, _⟩, c (ω ⟨i+n*j, _⟩))
    -- The Fin values have the same .val (j*n+i = i+n*j by ring)
    -- So the Fins are equal by proof irrelevance, and hence the pairs are equal
    simp only [show j.1 * n + i = i + n * j.1 from by ring]
  -- Step 3e: Error set equality
  have herr_set_eq : ∀ (ω : Fin ((n + 1) * n) → X),
      {x | L'.learn (fun i => (ω i, c (ω i))) x ≠ c x} =
      {x | boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (blockExtract (n + 1) n ω j i,
                           c (blockExtract (n + 1) n ω j i))) x) ≠ c x} := by
    intro ω; ext x; simp [hlearn_unfold ω x]
  -- Step 3f: Subset
  have hsub : {ω | 7 * (n + 1) ≤ 12 *
      (Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate (n + 1) n j)).card} ⊆
      {xs | D {x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x} ≤ ENNReal.ofReal ε} := by
    intro ω hω
    rw [Set.mem_ofPred_eq, herr_set_eq ω]
    have hbound := boosted_sample_error_le_of_good_blocks D c (hc_meas c hcC) L
      rate (n + 1) n ω (by omega) hω
    exact le_trans hbound (ENNReal.ofReal_le_ofReal h7rate)
  -- Step 3g: Final composition
  exact le_trans hconc (MeasureTheory.measure_mono hsub)
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    [MeasurableHypotheses X C]
    (hL_meas : ∀ (L : BatchLearner X Bool), LearnEvalMeasurable L)
    (hul : UniversalLearnable X C) :
    PACLearnable X C := by
  have hc_meas : ∀ c ∈ C, Measurable c := MeasurableHypotheses.mem_measurable (C := C)
  obtain ⟨L, rate, hrate, huniv⟩ := hul
  have : MeasurableBatchLearner X L := ⟨hL_meas L⟩
  exact boost_two_thirds_to_pac X C L rate hrate huniv
