-- Prove2me | solution 1 for expected_condVar_coord_eq_half_resample
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T06:20:36.970485+00:00
-- url     : https://prove2.me/submissions/be6c7fe1-c255-4d78-8520-116336df9a4c

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

/-- **Per-coordinate global resampling identity (Efron–Stein heart of the ½).**
The expectation over `ω ~ μ.pi` of the coordinate-`i` conditional variance
`Var_i Z (ω) = variance (fun x => Z (update ω i x)) (μ i)` equals half the expected squared
single-coordinate resampling difference on the doubled product cube.
Source: van Handel APC550 §2.1 ; BLM Ch.3 Thm 3.1. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    (∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ))
      = (∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
          ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by
  classical
  -- ============================================================
  -- Inlined: single-coordinate-fiber symmetrization (β := α i, non-polymorphic):
  --   Var(W) = ½∫∫(W x − W x')²  for W ∈ L²(μ i).
  -- ============================================================
  have varsym : ∀ {W : α i → ℝ}, MemLp W 2 (μ i) →
      variance W (μ i) = (∫ p, (W p.1 - W p.2) ^ 2 ∂((μ i).prod (μ i))) / 2 := by
    intro W hW
    set τ := (μ i).prod (μ i) with hτ
    have hWae : AEMeasurable W (μ i) := hW.aestronglyMeasurable.aemeasurable
    have mpfst : MeasurePreserving (Prod.fst : α i × α i → α i) τ (μ i) :=
      MeasureTheory.measurePreserving_fst
    have mpsnd : MeasurePreserving (Prod.snd : α i × α i → α i) τ (μ i) :=
      MeasureTheory.measurePreserving_snd
    set A : α i × α i → ℝ := fun p => W p.1 with hA
    set B : α i × α i → ℝ := fun p => W p.2 with hB
    have hAmem : MemLp A 2 τ := hW.comp_fst _
    have hBmem : MemLp B 2 τ := hW.comp_snd _
    have hvarA : variance A τ = variance W (μ i) := mpfst.variance_fun_comp hWae
    have hindep : IndepFun A B τ := by rw [hτ, hA, hB]; exact indepFun_prod₀ hWae hWae
    have e1 : Measure.map A τ = Measure.map W (μ i) := by
      rw [hA, show (fun p : α i × α i => W p.1) = W ∘ Prod.fst from rfl,
        ← AEMeasurable.map_map_of_aemeasurable (mpfst.map_eq ▸ hWae) measurable_fst.aemeasurable,
        mpfst.map_eq]
    have e2 : Measure.map B τ = Measure.map W (μ i) := by
      rw [hB, show (fun p : α i × α i => W p.2) = W ∘ Prod.snd from rfl,
        ← AEMeasurable.map_map_of_aemeasurable (mpsnd.map_eq ▸ hWae) measurable_snd.aemeasurable,
        mpsnd.map_eq]
    have hident : IdentDistrib A B τ τ :=
      ⟨hAmem.aestronglyMeasurable.aemeasurable, hBmem.aestronglyMeasurable.aemeasurable,
        by rw [e1, e2]⟩
    -- inlined keystone Var(A) = ½∫(A−B)² for indep + identDistrib L².
    have key : variance A τ = (∫ p, (A p - B p) ^ 2 ∂τ) / 2 := by
      have hWm : AEStronglyMeasurable A τ := hAmem.aestronglyMeasurable
      have hW'm : AEStronglyMeasurable B τ := hBmem.aestronglyMeasurable
      have hWint : Integrable A τ := hAmem.integrable one_le_two
      have hW'int : Integrable B τ := hBmem.integrable one_le_two
      have hWsq : Integrable (fun ω => A ω ^ 2) τ := by simpa [pow_two] using hAmem.integrable_sq
      have hW'sq : Integrable (fun ω => B ω ^ 2) τ := by simpa [pow_two] using hBmem.integrable_sq
      have hWW' : Integrable (fun ω => A ω * B ω) τ := hindep.integrable_mul hWint hW'int
      have hexpand : ∀ ω, (A ω - B ω) ^ 2 = A ω ^ 2 - 2 * (A ω * B ω) + B ω ^ 2 := by
        intro ω; ring
      have hsplit : ∫ ω, (A ω - B ω) ^ 2 ∂τ
          = (∫ ω, A ω ^ 2 ∂τ) - 2 * (∫ ω, A ω * B ω ∂τ) + (∫ ω, B ω ^ 2 ∂τ) := by
        calc ∫ ω, (A ω - B ω) ^ 2 ∂τ
            = ∫ ω, (A ω ^ 2 - 2 * (A ω * B ω) + B ω ^ 2) ∂τ := by simp_rw [hexpand]
          _ = (∫ ω, (A ω ^ 2 - 2 * (A ω * B ω)) ∂τ) + ∫ ω, B ω ^ 2 ∂τ :=
              integral_add (hWsq.sub (hWW'.const_mul 2)) hW'sq
          _ = ((∫ ω, A ω ^ 2 ∂τ) - ∫ ω, 2 * (A ω * B ω) ∂τ) + ∫ ω, B ω ^ 2 ∂τ := by
              rw [integral_sub hWsq (hWW'.const_mul 2)]
          _ = (∫ ω, A ω ^ 2 ∂τ) - 2 * (∫ ω, A ω * B ω ∂τ) + (∫ ω, B ω ^ 2 ∂τ) := by
              rw [integral_const_mul]
      have hmul : ∫ ω, A ω * B ω ∂τ = (∫ ω, A ω ∂τ) * (∫ ω, B ω ∂τ) :=
        hindep.integral_fun_mul_eq_mul_integral hWm hW'm
      have hEeq : ∫ ω, B ω ∂τ = ∫ ω, A ω ∂τ := hident.symm.integral_eq
      have hEsq : ∫ ω, B ω ^ 2 ∂τ = ∫ ω, A ω ^ 2 ∂τ := by
        have := (hident.symm.comp (measurable_id.pow_const 2)).integral_eq
        simpa using this
      rw [variance_eq_sub hAmem, hsplit, hmul, hEeq, hEsq]
      have hsq : τ[A ^ 2] = ∫ ω, A ω ^ 2 ∂τ := by simp [Pi.pow_apply]
      have hEW : τ[A] = ∫ ω, A ω ∂τ := rfl
      rw [hsq, hEW]; ring
    rw [hvarA] at key; rw [← key]
  -- ============================================================
  -- Inlined: single-coordinate resample map is measure-preserving.
  -- ============================================================
  have update_mp : MeasurePreserving (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
    have hmeas : Measurable (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2) := by
      fun_prop
    refine ⟨hmeas, ?_⟩
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
        = (Set.univ.pi (fun j => if j = i then Set.univ else s j)) ×ˢ (s i) := by
      ext ⟨ω, x⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
      constructor
      · intro h
        refine ⟨fun j => ?_, ?_⟩
        · split_ifs with hj
          · trivial
          · have := h j; rwa [Function.update_of_ne hj] at this
        · have := h i; rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ j
        by_cases hj : j = i
        · subst hj; rwa [Function.update_self]
        · rw [Function.update_of_ne hj]; have := h1 j; rwa [if_neg hj] at this
    rw [hpre, Measure.prod_prod]
    have hA : Measure.pi μ (Set.univ.pi (fun j => if j = i then Set.univ else s j))
        = ∏ j, μ j (if j = i then Set.univ else s j) := by rw [Measure.pi_pi]
    rw [hA]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
        ← Finset.prod_erase_mul _ (fun j => μ j (s j)) (Finset.mem_univ i)]
    have herase : (∏ x ∈ Finset.univ.erase i, μ x (if x = i then univ else s x))
        = ∏ x ∈ Finset.univ.erase i, μ x (s x) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [herase, if_pos rfl, measure_univ, mul_one]
  -- ============================================================
  -- Main proof body (= Bot4EfronSteinPerCoord.expected_condVar_coord_eq_half_resample).
  -- ============================================================
  set e : (∀ j, α j) × α i → (∀ j, α j) := fun p => Function.update p.1 i p.2 with he
  have heMP : MeasurePreserving e ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := update_mp
  have hemeas : Measurable e := heMP.measurable
  set F : (∀ j, α j) × α i → ℝ := fun p => Z (Function.update p.1 i p.2) with hF
  have hFmem : MemLp F 2 ((Measure.pi μ).prod (μ i)) := hZ.comp_measurePreserving heMP
  have hFint : Integrable F ((Measure.pi μ).prod (μ i)) := hFmem.integrable (by norm_num)
  have hFsq : Integrable (fun p => (F p) ^ 2) ((Measure.pi μ).prod (μ i)) := hFmem.integrable_sq
  have hfib1 : ∀ᵐ ω ∂(Measure.pi μ), Integrable (fun x => Z (Function.update ω i x)) (μ i) :=
    hFint.prod_right_ae
  have hfib2 : ∀ᵐ ω ∂(Measure.pi μ),
      Integrable (fun x => (Z (Function.update ω i x)) ^ 2) (μ i) := hFsq.prod_right_ae
  have hfibMemLp : ∀ᵐ ω ∂(Measure.pi μ),
      MemLp (fun x => Z (Function.update ω i x)) 2 (μ i) := by
    filter_upwards [hfib1, hfib2] with ω h1 h2
    exact (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).2 h2
  have hLHS : (∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ))
      = (∫ ω, (∫ q, (Z (Function.update ω i q.1) - Z (Function.update ω i q.2)) ^ 2
            ∂((μ i).prod (μ i))) ∂(Measure.pi μ)) / 2 := by
    rw [← integral_div]
    refine integral_congr_ae ?_
    filter_upwards [hfibMemLp] with ω hω
    rw [varsym hω]
  set H : (∀ j, α j) → ℝ := fun η => ∫ x', (Z η - Z (Function.update η i x')) ^ 2 ∂(μ i)
    with hH
  have hrMP : MeasurePreserving
      (fun p : (∀ j, α j) × (∀ j, α j) => Function.update p.1 i (p.2 i))
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
    have hmid : MeasurePreserving (Prod.map (id : (∀ j, α j) → (∀ j, α j)) (Function.eval i))
        ((Measure.pi μ).prod (Measure.pi μ)) ((Measure.pi μ).prod (μ i)) :=
      (MeasurePreserving.id (Measure.pi μ)).prod (measurePreserving_eval μ i)
    have := heMP.comp hmid
    exact this
  have hrmeas : Measurable
      (fun p : (∀ j, α j) × (∀ j, α j) => Function.update p.1 i (p.2 i)) := hrMP.measurable
  have hZfst : MemLp (fun p : (∀ j, α j) × (∀ j, α j) => Z p.1) 2
      ((Measure.pi μ).prod (Measure.pi μ)) := hZ.comp_fst _
  have hZres : MemLp (fun p : (∀ j, α j) × (∀ j, α j) => Z (Function.update p.1 i (p.2 i))) 2
      ((Measure.pi μ).prod (Measure.pi μ)) := hZ.comp_measurePreserving hrMP
  have hRHSint : Integrable
      (fun p : (∀ j, α j) × (∀ j, α j) =>
        (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2)
      ((Measure.pi μ).prod (Measure.pi μ)) := (hZfst.sub hZres).integrable_sq
  have hRHS : (∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
        ∂((Measure.pi μ).prod (Measure.pi μ))) = ∫ η, H η ∂(Measure.pi μ) := by
    rw [integral_prod _ hRHSint]
    refine integral_congr_ae ?_
    filter_upwards [hfib1] with η hηint
    simp only [hH]
    have hG : AEStronglyMeasurable (fun x' => (Z η - Z (Function.update η i x')) ^ 2) (μ i) :=
      ((aestronglyMeasurable_const.sub hηint.aestronglyMeasurable).pow 2)
    rw [← (measurePreserving_eval μ i).map_eq] at hG ⊢
    rw [integral_map (φ := Function.eval i) (measurePreserving_eval μ i).aemeasurable hG]
  have hcollapse : (∫ ω, (∫ q, (Z (Function.update ω i q.1) - Z (Function.update ω i q.2)) ^ 2
            ∂((μ i).prod (μ i))) ∂(Measure.pi μ))
      = ∫ η, H η ∂(Measure.pi μ) := by
    have hinner : ∀ᵐ ω ∂(Measure.pi μ),
        (∫ q, (Z (Function.update ω i q.1) - Z (Function.update ω i q.2)) ^ 2
            ∂((μ i).prod (μ i)))
          = ∫ x, H (Function.update ω i x) ∂(μ i) := by
      filter_upwards [hfibMemLp] with ω hWmem
      have hdbl : Integrable
          (fun q : α i × α i =>
            (Z (Function.update ω i q.1) - Z (Function.update ω i q.2)) ^ 2)
          ((μ i).prod (μ i)) := by
        have := ((hWmem.comp_fst _).sub (hWmem.comp_snd _)).integrable_sq
        simpa using this
      rw [integral_prod _ hdbl]
      refine integral_congr_ae (.of_forall (fun x => ?_))
      simp only [hH]
      refine integral_congr_ae (.of_forall (fun x' => ?_))
      simp only [Function.update_idem]
    rw [integral_congr_ae hinner]
    have hHint : Integrable H (Measure.pi μ) := by
      have hG : Integrable
          (fun p : (∀ j, α j) × α i =>
            (Z p.1 - Z (Function.update p.1 i p.2)) ^ 2)
          ((Measure.pi μ).prod (μ i)) := by
        have hZf : MemLp (fun p : (∀ j, α j) × α i => Z p.1) 2
            ((Measure.pi μ).prod (μ i)) := hZ.comp_fst _
        have := (hZf.sub hFmem).integrable_sq
        simpa [hF] using this
      have := hG.integral_prod_left
      simpa only [hH] using this
    have hHint_comp : Integrable (fun p => H (e p)) ((Measure.pi μ).prod (μ i)) :=
      heMP.integrable_comp_of_integrable hHint
    calc (∫ ω, ∫ x, H (Function.update ω i x) ∂(μ i) ∂(Measure.pi μ))
        = ∫ p, H (e p) ∂((Measure.pi μ).prod (μ i)) := by
          rw [integral_prod _ hHint_comp]
      _ = ∫ η, H η ∂(Measure.pi μ) := by
          conv_rhs => rw [← heMP.map_eq]
          rw [integral_map hemeas.aemeasurable]
          rw [heMP.map_eq]
          exact hHint.aestronglyMeasurable
  rw [hLHS, hRHS, hcollapse]
