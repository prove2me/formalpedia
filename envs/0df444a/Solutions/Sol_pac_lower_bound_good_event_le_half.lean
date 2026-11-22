-- Prove2me | solution 1 for pac_lower_bound_good_event_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:53.223784+00:00
-- url     : https://prove2.me/submissions/74e9edfa-f2f1-4e04-8efb-effe61b2f6a2

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
theorem _root_.solution
    (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    {T : Finset X} (hTne : T.Nonempty) (L : BatchLearner X Bool)
    (m : ℕ) (c₀ : X → Bool) (ε : ℝ) (hε1 : ε ≤ 1 / 4)
    (hcount : 2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
      (Finset.univ.filter fun t : ↥T =>
        c₀ ((↑t : X)) ≠ L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
      ≤ T.card).card ≤ Fintype.card (Fin m → ↥T)) :
    ∃ D : MeasureTheory.Measure X, MeasureTheory.IsProbabilityMeasure D ∧
      MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal ε } ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  let msT : MeasurableSpace ↥T := ⊤
  have : @MeasurableSingletonClass ↥T ⊤ :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hTne_type : Nonempty ↥T := hTne.coe_sort
  have hTpos : 0 < Fintype.card ↥T := Fintype.card_pos_iff.mpr hTne_type
  let D_sub := @uniformMeasure ↥T ⊤ _ hTne_type
  have hD_sub_prob : @MeasureTheory.IsProbabilityMeasure ↥T ⊤ D_sub :=
    @uniformMeasure_isProbability ↥T ⊤ _ hTne_type hTpos
  have hval_meas : @Measurable ↥T X ⊤ _ Subtype.val :=
    fun _ _ => MeasurableSpace.measurableSet_top
  let D := @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub
  have hDprob : MeasureTheory.IsProbabilityMeasure D := by
    constructor
    show D Set.univ = 1
    simp only [D, MeasureTheory.Measure.map_apply hval_meas MeasurableSet.univ]
    simp_all
  refine ⟨D, hDprob, ?_⟩
  have hval_emb : @MeasurableEmbedding ↥T X ⊤ _ Subtype.val := {
    injective := Subtype.val_injective
    measurable := hval_meas
    measurableSet_image' := fun {s} _ => by
      exact Set.Finite.measurableSet (Set.Finite.subset T.finite_toSet
        (fun x hx => by obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx; exact Finset.mem_coe.mpr hy)) }
  have hD_val : ∀ S : Set X, D S = D_sub (Subtype.val ⁻¹' S) :=
    fun S => hval_emb.map_apply D_sub S
  let valProd : (Fin m → ↥T) → (Fin m → X) := fun xs i => (xs i).val
  have hvalProd_emb : @MeasurableEmbedding (Fin m → ↥T) (Fin m → X)
      (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤))
      MeasurableSpace.pi valProd := {
    injective := fun a b hab => funext fun i => Subtype.val_injective (congr_fun hab i)
    measurable := by
      rw [@measurable_pi_iff]; intro i
      exact hval_meas.comp (@measurable_pi_apply (Fin m) (fun _ => ↥T)
        (fun _ => (⊤ : MeasurableSpace ↥T)) i)
    measurableSet_image' := fun {s} _ =>
      (Set.toFinite s |>.image valProd).measurableSet }
  have hpi_map : MeasureTheory.Measure.pi (fun _ : Fin m => D) =
      (@MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub)).map valProd := by
    let : ∀ (_ : Fin m), MeasureTheory.SigmaFinite
        (@MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub) := fun _ => by
      change MeasureTheory.SigmaFinite D; exact inferInstance
    conv_lhs =>
      rw [show (fun (_ : Fin m) => D) =
        fun (_ : Fin m) => @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub from rfl]
    symm
    convert @MeasureTheory.Measure.pi_map_pi (Fin m) inferInstance
      (fun _ => ↥T) (fun _ => X) (fun _ => (⊤ : MeasurableSpace ↥T))
      (fun _ => D_sub) inferInstance (fun _ => @Subtype.val X (· ∈ T))
      inferInstance (fun _ => hval_meas.aemeasurable) using 1
  have hpi_val : ∀ S : Set (Fin m → X),
      MeasureTheory.Measure.pi (fun _ : Fin m => D) S =
      @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub) (valProd ⁻¹' S) := fun S => by
    rw [hpi_map]; exact hvalProd_emb.map_apply _ S
  set good_X : Set (Fin m → X) := { xs |
    D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
      ≤ ENNReal.ofReal ε } with good_X_def
  set good_quarter : Set (Fin m → X) := { xs |
    D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
      ≤ ENNReal.ofReal (1 / 4 : ℝ) } with good_quarter_def
  set count_finset := Finset.univ.filter fun xs : Fin m → ↥T =>
    (Finset.univ.filter fun t : ↥T =>
      c₀ ((↑t : X)) ≠
        L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
    ≤ T.card with count_finset_def
  have hgood_sub : good_X ⊆ good_quarter := by
    intro xs hxs
    simp only [good_X_def, good_quarter_def, Set.mem_ofPred_eq] at hxs ⊢
    exact le_trans hxs (ENNReal.ofReal_le_ofReal hε1)
  have hpre_eq : valProd ⁻¹' good_quarter = (↑count_finset : Set (Fin m → ↥T)) := by
    ext xs_T
    simp only [Set.mem_preimage, good_quarter_def, Set.mem_ofPred_eq, valProd,
      count_finset_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    set h_val := L.learn (fun i => ((↑(xs_T i) : X), c₀ (↑(xs_T i))))
    have herr : D { x | h_val x ≠ c₀ x } =
        D_sub { t : ↥T | c₀ (↑t) ≠ h_val (↑t) } := by
      rw [hD_val]; congr 1; ext ⟨t, _⟩; exact ne_comm
    have hunif : D_sub { t : ↥T | c₀ (↑t) ≠ h_val (↑t) } =
        ((Finset.univ.filter fun t : ↥T => c₀ (↑t) ≠ h_val (↑t)).card : ENNReal) /
          (T.card : ENNReal) := by
      simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      rw [@MeasureTheory.Measure.count_apply_finite' ↥T ⊤ _
        (Set.toFinite _) MeasurableSpace.measurableSet_top]
      simp only [Fintype.card_coe, one_div, ne_eq, Set.Finite.toFinset_ofPred,
        Finset.univ_eq_attach]
      rw [ENNReal.div_eq_inv_mul]
    rw [herr, hunif]
    set k := (Finset.univ.filter fun t : ↥T => c₀ (↑t) ≠ h_val (↑t)).card
    have hd_ne : (T.card : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by
      rw [← Fintype.card_coe]; exact Nat.pos_iff_ne_zero.mp hTpos)
    have hd_nt : (T.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top T.card
    have hquarter : ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]; norm_num
    constructor
    · intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt] at hle
      rw [hquarter, mul_comm] at hle
      have h4 : (k : ENNReal) * 4 ≤ (T.card : ENNReal) :=
        calc (k : ENNReal) * 4
            ≤ (T.card : ENNReal) * (4 : ENNReal)⁻¹ * 4 := mul_le_mul_left hle 4
          _ = (T.card : ENNReal) := by
              rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
      exact_mod_cast h4
    · intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt, hquarter, mul_comm]
      have hk4 : (k : ENNReal) * 4 ≤ (T.card : ENNReal) := by exact_mod_cast hle
      calc (k : ENNReal) = (k : ENNReal) * 4 * (4 : ENNReal)⁻¹ := by
              rw [mul_assoc, mul_comm 4 (4 : ENNReal)⁻¹,
                  ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
            _ ≤ (T.card : ENNReal) * (4 : ENNReal)⁻¹ := mul_le_mul_left hk4 _
  have hgoal_eq : MeasureTheory.Measure.pi (fun _ : Fin m => D) good_quarter =
      @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub) (↑count_finset) := by
    rw [hpi_val good_quarter, hpre_eq]
  have hpi_sub_bound : @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
      (fun _ => D_sub) (↑count_finset) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    set μ_pi := @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
      (fun _ => D_sub) with hμ_pi_def
    have inst_msc_pi : @MeasurableSingletonClass (Fin m → ↥T)
        (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤)) :=
      @Pi.instMeasurableSingletonClass (Fin m) (fun _ => ↥T) (fun _ => ⊤)
        inferInstance (fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩)
    have : @MeasureTheory.IsFiniteMeasure ↥T ⊤ D_sub := by
      constructor; rw [hD_sub_prob.measure_univ]; exact ENNReal.one_lt_top
    have : @MeasureTheory.SigmaFinite ↥T ⊤ D_sub :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite ↥T ⊤ D_sub inferInstance
    have hD_sub_singleton : ∀ t : ↥T, D_sub {t} = 1 / (T.card : ENNReal) := by
      intro t
      simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      simp_all
    have hpi_singleton : ∀ xs : Fin m → ↥T,
        μ_pi {xs} = (1 / (T.card : ENNReal)) ^ m := by
      simp_all
    have hsum_eq : μ_pi (↑count_finset) = ∑ xs ∈ count_finset, μ_pi {xs} :=
      (@MeasureTheory.sum_measure_singleton (Fin m → ↥T)
        (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤)) μ_pi
        count_finset inst_msc_pi).symm
    rw [hsum_eq]
    simp only [hpi_singleton, Finset.sum_const, nsmul_eq_mul]
    have hd_ne : (T.card : ENNReal) ^ m ≠ 0 :=
      pow_ne_zero m (Nat.cast_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr hTne)))
    have hd_ne_top : (T.card : ENNReal) ^ m ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top T.card)
    rw [show (count_finset.card : ENNReal) * (1 / (T.card : ENNReal)) ^ m =
        (count_finset.card : ENNReal) / (T.card : ENNReal) ^ m from by
      rw [one_div, ← ENNReal.inv_pow, div_eq_mul_inv]]
    rw [ENNReal.div_le_iff hd_ne hd_ne_top]
    have h_ennreal : (2 * count_finset.card : ENNReal) ≤ (T.card : ENNReal) ^ m := by
      rw [show (T.card : ENNReal) ^ m = ((T.card ^ m : ℕ) : ENNReal) from by push_cast; rfl]
      push_cast
      have hcard_eq : Fintype.card (Fin m → ↥T) = T.card ^ m := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      have h_le_card : 2 * count_finset.card ≤ Fintype.card (Fin m → ↥T) := by
        simpa [count_finset_def] using hcount
      rw [hcard_eq] at h_le_card
      exact_mod_cast h_le_card
    calc (count_finset.card : ENNReal)
        = (count_finset.card : ENNReal) * 1 := (mul_one _).symm
      _ = (count_finset.card : ENNReal) * (2 * (2 : ENNReal)⁻¹) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      _ = (count_finset.card : ENNReal) * 2 * (2 : ENNReal)⁻¹ := by ring
      _ = (2 * count_finset.card : ENNReal) * (2 : ENNReal)⁻¹ := by ring
      _ ≤ (T.card : ENNReal) ^ m * (2 : ENNReal)⁻¹ :=
          mul_le_mul_left h_ennreal _
      _ = ENNReal.ofReal (1 / 2 : ℝ) * (T.card : ENNReal) ^ m := by
          rw [show ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ from by
            rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]; norm_num]
          ring
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D) good_X
      ≤ MeasureTheory.Measure.pi (fun _ : Fin m => D) good_quarter :=
        MeasureTheory.measure_mono hgood_sub
    _ = @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
          (fun _ => D_sub) (↑count_finset) := hgoal_eq
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := hpi_sub_bound
