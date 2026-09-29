-- Prove2me | solution 1 for efron_stein_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T17:22:21.136462+00:00
-- url     : https://prove2.me/submissions/6ebfa7f9-36a1-4233-8155-68d4a39cb213

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_variance_partialIntegral_le_integral_variance
import Theorems.Thm_condExp_comap_fst_eq_partial_integral
import Theorems.Thm_efron_stein_condExp_comap_snd_eq_partial_integral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 1000000

private lemma measure_pi_eq_of_fintype
    {κ : Type*} {π : κ → Type*} [∀ k, MeasurableSpace (π k)]
    (inst1 inst2 : Fintype κ) (ν : ∀ k, Measure (π k)) [∀ k, SigmaFinite (ν k)] :
    @Measure.pi κ π inst1 (fun _ => inferInstance) ν
      = @Measure.pi κ π inst2 (fun _ => inferInstance) ν := by
  letI := inst1
  refine Measure.pi_eq (μ := ν) (μ' := @Measure.pi κ π inst2 (fun _ => inferInstance) ν) ?_
  intro t ht
  have h2 : (@Measure.pi κ π inst2 (fun _ => inferInstance) ν) (Set.univ.pi t)
      = ∏ k ∈ (@Finset.univ κ inst2), ν k (t k) := by
    letI := inst2
    exact Measure.pi_pi ν t
  rw [h2]
  apply Finset.prod_congr
  · ext k
    simp
  · intro k hk
    rfl

private lemma integral_condVar_comap_snd_eq_integral_variance
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ]
    (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    (ρ.prod σ)[Var[W; ρ.prod σ | MeasurableSpace.comap Prod.snd inferInstance]]
      = ∫ y, variance (fun x => W (x, y)) ρ ∂σ := by
  classical
  let m : MeasurableSpace (β × γ) := MeasurableSpace.comap Prod.snd inferInstance
  have hm : m ≤ Prod.instMeasurableSpace := by
    simpa [m] using
      (measurable_snd.comap_le :
        MeasurableSpace.comap (Prod.snd : β × γ → γ) inferInstance
          ≤ Prod.instMeasurableSpace)
  have hWint : Integrable W (ρ.prod σ) := hW.integrable one_le_two
  have hcond :
      (ρ.prod σ)[W | m] =ᵐ[ρ.prod σ] fun p => ∫ x, W (x, p.2) ∂ρ := by
    simpa [m] using
      efron_stein_condExp_comap_snd_eq_partial_integral
        ρ σ hWint
  have hcenterSq_int :
      Integrable (fun p : β × γ => (W p - (ρ.prod σ)[W | m] p) ^ 2) (ρ.prod σ) := by
    have hcenter : MemLp (fun p : β × γ => W p - (ρ.prod σ)[W | m] p) 2
        (ρ.prod σ) := by
      exact hW.sub (hW.condExp one_le_two)
    simpa [pow_two] using hcenter.integrable_sq
  have hpartialSq_int :
      Integrable (fun p : β × γ => (W p - ∫ x, W (x, p.2) ∂ρ) ^ 2) (ρ.prod σ) := by
    refine hcenterSq_int.congr ?_
    filter_upwards [hcond] with p hp
    simp [hp]
  have hW_fib_int : ∀ᵐ y ∂σ, Integrable (fun x => W (x, y)) ρ := hWint.prod_left_ae
  calc
    (ρ.prod σ)[Var[W; ρ.prod σ | m]]
        = ∫ p, (W p - (ρ.prod σ)[W | m] p) ^ 2 ∂(ρ.prod σ) := by
          rw [condVar]
          exact integral_condExp hm
    _ = ∫ p, (W p - ∫ x, W (x, p.2) ∂ρ) ^ 2 ∂(ρ.prod σ) := by
          exact integral_congr_ae (hcond.mono fun p hp => by simp [hp])
    _ = ∫ y, ∫ x, (W (x, y) - ∫ x', W (x', y) ∂ρ) ^ 2 ∂ρ ∂σ := by
          rw [integral_prod_symm _ hpartialSq_int]
    _ = ∫ y, variance (fun x => W (x, y)) ρ ∂σ := by
          refine integral_congr_ae ?_
          filter_upwards [hW_fib_int] with y hy
          rw [variance_eq_integral hy.aestronglyMeasurable.aemeasurable]

private lemma variance_sub_partialIntegral_eq_integral_variance
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ]
    (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    variance W (ρ.prod σ) - variance (fun y => ∫ x, W (x, y) ∂ρ) σ
      = ∫ y, variance (fun x => W (x, y)) ρ ∂σ := by
  classical
  let m : MeasurableSpace (β × γ) := MeasurableSpace.comap Prod.snd inferInstance
  have hm : m ≤ Prod.instMeasurableSpace := by
    simpa [m] using
      (measurable_snd.comap_le :
        MeasurableSpace.comap (Prod.snd : β × γ → γ) inferInstance
          ≤ Prod.instMeasurableSpace)
  have hWint : Integrable W (ρ.prod σ) := hW.integrable one_le_two
  have hcond :
      (ρ.prod σ)[W | m] =ᵐ[ρ.prod σ] fun p => ∫ x, W (x, p.2) ∂ρ := by
    simpa [m] using
      efron_stein_condExp_comap_snd_eq_partial_integral
        ρ σ hWint
  have hLOTV :
      (ρ.prod σ)[Var[W; ρ.prod σ | m]] + Var[(ρ.prod σ)[W | m]; ρ.prod σ]
        = Var[W; ρ.prod σ] :=
    integral_condVar_add_variance_condExp hm hW
  have hpart_int : Integrable (fun y => ∫ x, W (x, y) ∂ρ) σ := hWint.integral_prod_right
  have hvarCE :
      Var[(ρ.prod σ)[W | m]; ρ.prod σ]
        = variance (fun y => ∫ x, W (x, y) ∂ρ) σ := by
    calc
      Var[(ρ.prod σ)[W | m]; ρ.prod σ]
          = Var[(fun p : β × γ => ∫ x, W (x, p.2) ∂ρ); ρ.prod σ] :=
            variance_congr hcond
      _ = variance (fun y => ∫ x, W (x, y) ∂ρ) σ := by
            exact measurePreserving_snd.variance_fun_comp hpart_int.aemeasurable
  have hcv := integral_condVar_comap_snd_eq_integral_variance ρ σ hW
  rw [hvarCE, hcv] at hLOTV
  linarith

private lemma integrable_variance_fiber_snd
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ]
    (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    Integrable (fun y => variance (fun x => W (x, y)) ρ) σ := by
  classical
  have hWint : Integrable W (ρ.prod σ) := hW.integrable one_le_two
  have hW_fib_int : ∀ᵐ y ∂σ, Integrable (fun x => W (x, y)) ρ := hWint.prod_left_ae
  set u : γ → ℝ := fun y => ∫ x, W (x, y) ∂ρ with hu
  let m : MeasurableSpace (β × γ) := MeasurableSpace.comap Prod.snd inferInstance
  have hcond : (ρ.prod σ)[W | m] =ᵐ[ρ.prod σ] fun p => u p.2 := by
    simpa [m, u, hu] using
      efron_stein_condExp_comap_snd_eq_partial_integral ρ σ hWint
  have hu_comp_mem : MemLp (fun p : β × γ => u p.2) 2 (ρ.prod σ) := by
    exact (hW.condExp one_le_two).ae_eq hcond
  have hcenter : MemLp (fun p : β × γ => W p - u p.2) 2 (ρ.prod σ) :=
    hW.sub hu_comp_mem
  have hsq_int : Integrable (fun p : β × γ => (W p - u p.2) ^ 2) (ρ.prod σ) := by
    simpa [pow_two] using hcenter.integrable_sq
  have hinner_int : Integrable (fun y => ∫ x, (W (x, y) - u y) ^ 2 ∂ρ) σ := by
    simpa [u, hu] using hsq_int.integral_prod_right
  exact hinner_int.congr (by
    filter_upwards [hW_fib_int] with y hy
    rw [variance_eq_integral hy.aestronglyMeasurable.aemeasurable])


private lemma three_factor_increment_le
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (ρ : Measure β) [IsProbabilityMeasure ρ]
    (σ : Measure γ) [IsProbabilityMeasure σ]
    (τ : Measure δ) [IsProbabilityMeasure τ]
    {H : (β × γ) × δ → ℝ} (hH : MemLp H 2 ((ρ.prod σ).prod τ)) :
    variance (fun p : β × γ => ∫ d, H (p, d) ∂τ) (ρ.prod σ)
      - variance (fun y : γ => ∫ x, (∫ d, H ((x, y), d) ∂τ) ∂ρ) σ
      ≤ ∫ y, ∫ d, variance (fun x => H ((x, y), d)) ρ ∂τ ∂σ := by
  classical
  set G : β × γ → ℝ := fun p => ∫ d, H (p, d) ∂τ with hG
  have hHint : Integrable H ((ρ.prod σ).prod τ) := hH.integrable one_le_two
  have hcondG :
      (((ρ.prod σ).prod τ)[H | MeasurableSpace.comap Prod.fst inferInstance])
        =ᵐ[((ρ.prod σ).prod τ)] fun q : (β × γ) × δ => G q.1 := by
    simpa [G, hG] using
      condExp_comap_fst_eq_partial_integral (ρ.prod σ) τ hHint
  have hG_comp_mem : MemLp (fun q : (β × γ) × δ => G q.1) 2 ((ρ.prod σ).prod τ) := by
    exact (hH.condExp one_le_two).ae_eq hcondG
  have hG_int_comp : Integrable (fun q : (β × γ) × δ => G q.1)
      ((ρ.prod σ).prod τ) :=
    hG_comp_mem.integrable one_le_two
  have hG_sq_comp : Integrable (fun q : (β × γ) × δ => (G q.1) ^ 2)
      ((ρ.prod σ).prod τ) := by
    simpa [pow_two] using hG_comp_mem.integrable_sq
  have hG_int : Integrable G (ρ.prod σ) :=
    hG_int_comp.of_comp_fst (IsProbabilityMeasure.ne_zero τ)
  have hG_sq : Integrable (fun p : β × γ => (G p) ^ 2) (ρ.prod σ) :=
    hG_sq_comp.of_comp_fst (IsProbabilityMeasure.ne_zero τ)
  have hGmem : MemLp G 2 (ρ.prod σ) :=
    (memLp_two_iff_integrable_sq hG_int.aestronglyMeasurable).2 hG_sq
  have hdiff := variance_sub_partialIntegral_eq_integral_variance ρ σ hGmem
  have hleft_int : Integrable (fun y => variance (fun x => G (x, y)) ρ) σ :=
    integrable_variance_fiber_snd ρ σ hGmem
  have hAssocSymm : MeasurePreserving
      (fun q : β × (γ × δ) => ((q.1, q.2.1), q.2.2))
      (ρ.prod (σ.prod τ)) ((ρ.prod σ).prod τ) := by
    exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ρ σ τ)
  have hH_by_x :
      MemLp (fun q : β × (γ × δ) => H ((q.1, q.2.1), q.2.2)) 2
        (ρ.prod (σ.prod τ)) := by
    simpa [Function.comp_def] using hH.comp_measurePreserving hAssocSymm
  have hR_pair_int :
      Integrable (fun yd : γ × δ => variance (fun x => H ((x, yd.1), yd.2)) ρ)
        (σ.prod τ) := by
    simpa using integrable_variance_fiber_snd ρ (σ.prod τ) hH_by_x
  have hright_int :
      Integrable (fun y => ∫ d, variance (fun x => H ((x, y), d)) ρ ∂τ) σ := by
    simpa using hR_pair_int.integral_prod_left
  have hPerm :
      MeasurePreserving (fun q : γ × (δ × β) => ((q.2.2, q.1), q.2.1))
        (σ.prod (τ.prod ρ)) ((ρ.prod σ).prod τ) := by
    let f1 : γ × (δ × β) → γ × (β × δ) := fun q => (q.1, (q.2.2, q.2.1))
    have hf1 : MeasurePreserving f1 (σ.prod (τ.prod ρ)) (σ.prod (ρ.prod τ)) := by
      exact (MeasurePreserving.id σ).prod (Measure.measurePreserving_swap (μ := τ) (ν := ρ))
    let f2 : γ × (β × δ) → (γ × β) × δ := fun q => ((q.1, q.2.1), q.2.2)
    have hf2 : MeasurePreserving f2 (σ.prod (ρ.prod τ)) ((σ.prod ρ).prod τ) := by
      exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc σ ρ τ)
    let f3 : (γ × β) × δ → (β × γ) × δ := fun q => ((q.1.2, q.1.1), q.2)
    have hf3 : MeasurePreserving f3 ((σ.prod ρ).prod τ) ((ρ.prod σ).prod τ) := by
      exact (Measure.measurePreserving_swap (μ := σ) (ν := ρ)).prod (MeasurePreserving.id τ)
    have hcomp := hf3.comp (hf2.comp hf1)
    exact hcomp
  have hH_perm :
      MemLp (fun q : γ × (δ × β) => H ((q.2.2, q.1), q.2.1)) 2
        (σ.prod (τ.prod ρ)) := by
    simpa [Function.comp_def] using hH.comp_measurePreserving hPerm
  have hH_perm_int :
      Integrable (fun q : γ × (δ × β) => H ((q.2.2, q.1), q.2.1))
        (σ.prod (τ.prod ρ)) :=
    hH_perm.integrable one_le_two
  have hH_perm_sq :
      Integrable (fun q : γ × (δ × β) => (H ((q.2.2, q.1), q.2.1)) ^ 2)
        (σ.prod (τ.prod ρ)) := by
    simpa [pow_two] using hH_perm.integrable_sq
  have hfib_int :
      ∀ᵐ y ∂σ, Integrable (fun z : δ × β => H ((z.2, y), z.1)) (τ.prod ρ) :=
    hH_perm_int.prod_right_ae
  have hfib_sq :
      ∀ᵐ y ∂σ, Integrable (fun z : δ × β => (H ((z.2, y), z.1)) ^ 2)
        (τ.prod ρ) :=
    hH_perm_sq.prod_right_ae
  have hpt : (fun y => variance (fun x => G (x, y)) ρ)
      ≤ᵐ[σ] (fun y => ∫ d, variance (fun x => H ((x, y), d)) ρ ∂τ) := by
    filter_upwards [hfib_int, hfib_sq] with y hy_int hy_sq
    have hWy : MemLp (fun z : δ × β => H ((z.2, y), z.1)) 2 (τ.prod ρ) :=
      (memLp_two_iff_integrable_sq hy_int.aestronglyMeasurable).2 hy_sq
    have hconv := variance_partialIntegral_le_integral_variance τ ρ hWy
    simpa [G, hG] using hconv
  calc
    variance (fun p : β × γ => ∫ d, H (p, d) ∂τ) (ρ.prod σ)
      - variance (fun y : γ => ∫ x, (∫ d, H ((x, y), d) ∂τ) ∂ρ) σ
        = ∫ y, variance (fun x => G (x, y)) ρ ∂σ := by
          simpa [G, hG] using hdiff
    _ ≤ ∫ y, ∫ d, variance (fun x => H ((x, y), d)) ρ ∂τ ∂σ := by
          exact integral_mono_ae hleft_int hright_int hpt


section ISec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

private lemma condExp_piFinset_eq_marginal (s : Finset ι) {Z : (∀ i, α i) → ℝ}
    (hZ : Integrable Z (Measure.pi μ)) :
    (Measure.pi μ)[Z | MeasurableSpace.comap (Finset.restrict s) inferInstance]
      =ᵐ[Measure.pi μ]
      fun ω => ∫ z : (∀ i : {i // ¬ i ∈ s}, α i),
          Z ((MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s)).symm
              ((MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s) ω).1, z))
          ∂(Measure.pi fun i : {i // ¬ i ∈ s} => μ i) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s) with he
  set ρ : Measure (∀ i : ↥s, α i) :=
    @Measure.pi ↥s (fun i : ↥s => α i) (Subtype.fintype (· ∈ s))
      (fun i : ↥s => inferInstance) (fun i : ↥s => μ i) with hρ
  set σ := Measure.pi fun i : {i // ¬ i ∈ s} => μ i with hσ
  have mpe : MeasurePreserving e (Measure.pi μ) (ρ.prod σ) := by
    rw [hρ, hσ, he]; exact measurePreserving_piEquivPiSubtypeProd μ (· ∈ s)
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  haveI : IsProbabilityMeasure σ := by rw [hσ]; infer_instance
  set F : (∀ i : ↥s, α i) × (∀ i : {i // ¬ i ∈ s}, α i) → ℝ :=
    fun q => Z (e.symm q) with hF
  have hZeq : Z = F ∘ e := by ext ω; simp [hF, he]
  have hFint : Integrable F (ρ.prod σ) := by
    rw [← mpe.integrable_comp_emb e.measurableEmbedding (g := F)]
    rw [← hZeq]; exact hZ
  set g : (∀ i, α i) → ℝ := fun ω => ∫ z, F ((e ω).1, z) ∂σ with hg
  have hcomap : MeasurableSpace.comap (Finset.restrict s)
      (inferInstance : MeasurableSpace (∀ i : ↥s, α i))
      = MeasurableSpace.comap e (MeasurableSpace.comap Prod.fst inferInstance) := by
    rw [MeasurableSpace.comap_comp]; rfl
  have hm : MeasurableSpace.comap (Finset.restrict s)
      (inferInstance : MeasurableSpace (∀ i : ↥s, α i))
      ≤ (inferInstance : MeasurableSpace (∀ i, α i)) :=
    (Finset.measurable_restrict s).comap_le
  set W' : (∀ i : ↥s, α i) × (∀ i : {i // ¬ i ∈ s}, α i) → ℝ :=
    fun q => ∫ y, F (q.1, y) ∂σ with hW'
  have hg_comp : g = W' ∘ e := by ext ω; simp [hg, hW', Function.comp]
  have hbrick : (ρ.prod σ)[F | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ρ.prod σ] W' :=
    condExp_comap_fst_eq_partial_integral ρ σ hFint
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hZ ?_ ?_ ?_).symm
  · intro t _ _
    have hW'int : Integrable W' (ρ.prod σ) := (integrable_condExp).congr hbrick
    have : Integrable g (Measure.pi μ) := by
      rw [hg_comp]; exact mpe.integrable_comp_of_integrable hW'int
    exact this.integrableOn
  · intro t ht _
    rw [hcomap] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have htrans_g : ∫ ω in e ⁻¹' u, g ω ∂(Measure.pi μ) = ∫ q in u, W' q ∂(ρ.prod σ) := by
      rw [hg_comp]; exact mpe.setIntegral_preimage_emb e.measurableEmbedding W' u
    have htrans_Z : ∫ ω in e ⁻¹' u, Z ω ∂(Measure.pi μ) = ∫ q in u, F q ∂(ρ.prod σ) := by
      rw [hZeq]; exact mpe.setIntegral_preimage_emb e.measurableEmbedding F u
    rw [htrans_g, htrans_Z]
    have hu_fst : MeasurableSet[MeasurableSpace.comap Prod.fst inferInstance] u := hu
    have hmfst : MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace _)
        ≤ (inferInstance : MeasurableSpace ((∀ i : ↥s, α i) × (∀ i : {i // ¬ i ∈ s}, α i))) :=
      measurable_fst.comap_le
    calc ∫ q in u, W' q ∂(ρ.prod σ)
        = ∫ q in u, ((ρ.prod σ)[F | MeasurableSpace.comap Prod.fst inferInstance]) q ∂(ρ.prod σ) := by
          exact integral_congr_ae (ae_restrict_of_ae hbrick.symm)
      _ = ∫ q in u, F q ∂(ρ.prod σ) := setIntegral_condExp hmfst hFint hu_fst
  · rw [hcomap]
    set h := (ρ.prod σ)[F | MeasurableSpace.comap Prod.fst inferInstance] with hh
    have hh_sm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance] h :=
      stronglyMeasurable_condExp
    have he_meas :
        @Measurable _ _ (MeasurableSpace.comap e (MeasurableSpace.comap Prod.fst inferInstance))
          (MeasurableSpace.comap Prod.fst inferInstance) e :=
      Measurable.of_comap_le le_rfl
    have hcomp_sm :
        StronglyMeasurable[MeasurableSpace.comap e (MeasurableSpace.comap Prod.fst inferInstance)]
          (h ∘ e) := hh_sm.comp_measurable he_meas
    have hg_ae : g =ᵐ[Measure.pi μ] (h ∘ e) := by
      rw [hg_comp]
      exact mpe.quasiMeasurePreserving.ae_eq_comp (g := W') (g' := h) hbrick.symm
    exact ⟨h ∘ e, hcomp_sm, hg_ae⟩


theorem solution
    (s : Finset ι) (i : ι) (hi : i ∉ s)
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    (Measure.pi μ)[Var[(Measure.pi μ)[Z | (Filtration.piFinset (X := α)) (insert i s)];
        Measure.pi μ | (Filtration.piFinset (X := α)) s]]
      ≤ ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
  classical
  let u : Finset ι := ({i} : Finset ι) ∪ s
  have hu : u = insert i s := by
    ext j
    simp [u, eq_comm]
  rw [← hu]
  letI : Fintype ↥u := Subtype.fintype (fun x => x ∈ u)
  let singleton : Finset ι := {i}
  have hdisj : Disjoint singleton s := by
    simpa [singleton, Finset.disjoint_singleton_left] using hi
  let σ : Measure (∀ j : s, α j) := Measure.pi fun j : s => μ j
  let τ : Measure (∀ j : {j // ¬ j ∈ u}, α j) :=
    Measure.pi fun j : {j // ¬ j ∈ u} => μ j
  haveI : IsProbabilityMeasure σ := by
    dsimp [σ]
    infer_instance
  haveI : IsProbabilityMeasure τ := by
    dsimp [τ]
    infer_instance
  let eSing : α i ≃ᵐ (∀ j : singleton, α j) :=
    (MeasurableEquiv.piUnique fun j : singleton => α j).symm
  have mpUnique :
      MeasurePreserving (MeasurableEquiv.piUnique fun j : singleton => α j)
        (Measure.pi fun j : singleton => μ j) (μ i) := by
    simpa [singleton] using
      (measurePreserving_piUnique (fun j : singleton => μ j))
  have mpSing :
      MeasurePreserving eSing (μ i) (Measure.pi fun j : singleton => μ j) := by
    simpa [eSing] using
      (MeasurePreserving.symm
        (MeasurableEquiv.piUnique fun j : singleton => α j) mpUnique)
  let eIS : (α i × (∀ j : s, α j)) ≃ᵐ (∀ j : u, α j) :=
    (MeasurableEquiv.prodCongr eSing (MeasurableEquiv.refl (∀ j : s, α j))).trans
      (by
        subst u
        exact MeasurableEquiv.piFinsetUnion α hdisj)
  have mpIS :
      MeasurePreserving eIS ((μ i).prod σ) (Measure.pi fun j : u => μ j) := by
    subst u
    have hprod :
        MeasurePreserving
          (MeasurableEquiv.prodCongr eSing (MeasurableEquiv.refl (∀ j : s, α j)))
          ((μ i).prod σ)
          ((Measure.pi fun j : singleton => μ j).prod σ) := by
      exact mpSing.prod (MeasurePreserving.id σ)
    have hunion :
        MeasurePreserving (MeasurableEquiv.piFinsetUnion α hdisj)
          ((Measure.pi fun j : singleton => μ j).prod σ)
      (Measure.pi fun j : (singleton ∪ s : Finset ι) => μ j) := by
      convert (measurePreserving_piFinsetUnion hdisj μ) using 1
      exact (measure_pi_eq_of_fintype _ _ (fun j : (singleton ∪ s : Finset ι) => μ j)).symm
    exact hunion.comp hprod
  let eFull : ((α i × (∀ j : s, α j)) × (∀ j : {j // ¬ j ∈ u}, α j)) ≃ᵐ
      (∀ j, α j) :=
    (MeasurableEquiv.prodCongr eIS
        (MeasurableEquiv.refl (∀ j : {j // ¬ j ∈ u}, α j))).trans
      (MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u)).symm
  have mpFull :
      MeasurePreserving eFull (((μ i).prod σ).prod τ) (Measure.pi μ) := by
    have hprod :
        MeasurePreserving
          (MeasurableEquiv.prodCongr eIS
            (MeasurableEquiv.refl (∀ j : {j // ¬ j ∈ u}, α j)))
          (((μ i).prod σ).prod τ)
          ((Measure.pi fun j : u => μ j).prod τ) := by
      exact mpIS.prod (MeasurePreserving.id τ)
    have hsplit :
        MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u)).symm
          ((Measure.pi fun j : u => μ j).prod τ) (Measure.pi μ) := by
      have hforward :
          MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u))
            (Measure.pi μ) ((Measure.pi fun j : u => μ j).prod τ) := by
        simpa [τ] using measurePreserving_piEquivPiSubtypeProd μ (· ∈ u)
      exact MeasurePreserving.symm
        (MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u)) hforward
    exact hsplit.comp hprod
  let H : ((α i × (∀ j : s, α j)) × (∀ j : {j // ¬ j ∈ u}, α j)) → ℝ :=
    fun q => Z (eFull q)
  have hH : MemLp H 2 (((μ i).prod σ).prod τ) := by
    exact hZ.comp_measurePreserving mpFull
  have hthree :
      variance (fun p : α i × (∀ j : s, α j) => ∫ d, H (p, d) ∂τ) ((μ i).prod σ)
        - variance (fun y : (∀ j : s, α j) =>
            ∫ x, (∫ d, H ((x, y), d) ∂τ) ∂(μ i)) σ
        ≤ ∫ y, ∫ d, variance (fun x => H ((x, y), d)) (μ i) ∂τ ∂σ :=
    three_factor_increment_le (μ i) σ τ hH
  let F : Finset ι → MeasurableSpace (∀ j, α j) :=
    fun t => (Filtration.piFinset (X := α)) t
  set Y : (∀ j, α j) → ℝ := (Measure.pi μ)[Z | F u] with hY
  have hZint : Integrable Z (Measure.pi μ) := hZ.integrable one_le_two
  have hYmem : MemLp Y 2 (Measure.pi μ) := by
    simpa [Y, hY, F] using hZ.condExp (m := F u)
  have hs_le : F s ≤ (inferInstance : MeasurableSpace (∀ j, α j)) := by
    simpa [F] using (Filtration.piFinset (X := α)).le s
  have hsu : s ⊆ u := by
    intro j hj
    simp [u, hj]
  have hmono : F s ≤ F u := by
    simpa [F] using (Filtration.piFinset (X := α)).mono hsu
  have hu_le : F u ≤ (inferInstance : MeasurableSpace (∀ j, α j)) := by
    simpa [F] using (Filtration.piFinset (X := α)).le u
  have hLOTV :
      (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
        + Var[(Measure.pi μ)[Y | F s]; Measure.pi μ] = Var[Y; Measure.pi μ] :=
    integral_condVar_add_variance_condExp hs_le hYmem
  have htower :
      (Measure.pi μ)[Y | F s] =ᵐ[Measure.pi μ] (Measure.pi μ)[Z | F s] := by
    rw [hY]
    exact condExp_condExp_of_le hmono hu_le
  have hVarTower :
      Var[(Measure.pi μ)[Y | F s]; Measure.pi μ]
        = Var[(Measure.pi μ)[Z | F s]; Measure.pi μ] :=
    variance_congr htower
  rw [hVarTower] at hLOTV
  have hcond_u :
      (Measure.pi μ)[Z | F u] =ᵐ[Measure.pi μ]
        fun ω => ∫ d : (∀ j : {j // ¬ j ∈ u}, α j),
          Z ((MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u)).symm
              ((MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u) ω).1, d)) ∂τ := by
    exact condExp_piFinset_eq_marginal μ u hZint
  have hYae :
      Y =ᵐ[Measure.pi μ]
        fun ω => ∫ d : (∀ j : {j // ¬ j ∈ u}, α j), H ((eFull.symm ω).1, d) ∂τ := by
    rw [hY]
    refine hcond_u.trans ?_
    exact Filter.Eventually.of_forall (fun ω => by
      refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
      simp only [H]
      congr 1
      let A : (α i × (∀ j : s, α j)) × (∀ j : {j // ¬ j ∈ u}, α j) ≃ᵐ
          (∀ j : u, α j) × (∀ j : {j // ¬ j ∈ u}, α j) :=
        MeasurableEquiv.prodCongr eIS
          (MeasurableEquiv.refl (∀ j : {j // ¬ j ∈ u}, α j))
      let B : (∀ j, α j) ≃ᵐ
          (∀ j : u, α j) × (∀ j : {j // ¬ j ∈ u}, α j) :=
        MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ u)
      apply B.injective
      simp only [B, eFull, MeasurableEquiv.trans_apply, MeasurableEquiv.trans_symm,
        MeasurableEquiv.apply_symm_apply]
      change ((B ω).1, d) = A ((A.symm (B ω)).1, d)
      ext x
      · change (B ω).1 x = eIS ((A.symm (B ω)).1) x
        exact congrFun (congrArg Prod.fst (A.apply_symm_apply (B ω))).symm x
      · rfl)
  set G : α i × (∀ j : s, α j) → ℝ := fun p => ∫ d, H (p, d) ∂τ with hG
  have hHint : Integrable H (((μ i).prod σ).prod τ) := hH.integrable one_le_two
  have hGint : Integrable G ((μ i).prod σ) := by
    simpa [G, hG] using hHint.integral_prod_left
  have mpFull_symm :
      MeasurePreserving eFull.symm (Measure.pi μ) (((μ i).prod σ).prod τ) :=
    MeasurePreserving.symm eFull mpFull
  have hYaeG : Y =ᵐ[Measure.pi μ] fun ω => G (eFull.symm ω).1 := by
    simpa [G, hG] using hYae
  have hGfst_int :
      Integrable
        (fun q : (α i × (∀ j : s, α j)) × (∀ j : {j // ¬ j ∈ u}, α j) => G q.1)
        (((μ i).prod σ).prod τ) :=
    hGint.comp_fst τ
  have mpProd_fst :
      MeasurePreserving
        (Prod.fst : (α i × (∀ j : s, α j)) × (∀ j : {j // ¬ j ∈ u}, α j) →
          α i × (∀ j : s, α j))
        (((μ i).prod σ).prod τ) ((μ i).prod σ) :=
    measurePreserving_fst
  have hvarY :
      Var[Y; Measure.pi μ] = variance G ((μ i).prod σ) := by
    calc
      Var[Y; Measure.pi μ]
          = Var[(fun ω => G (eFull.symm ω).1); Measure.pi μ] := variance_congr hYaeG
      _ = Var[(fun q : (α i × (∀ j : s, α j)) × (∀ j : {j // ¬ j ∈ u}, α j) =>
              G q.1); (((μ i).prod σ).prod τ)] := by
            exact mpFull_symm.variance_fun_comp hGfst_int.aemeasurable
      _ = variance G ((μ i).prod σ) := by
            exact mpProd_fst.variance_fun_comp hGint.aemeasurable
  let D := {j // ¬ j ∈ s}
  letI : Fintype D := Subtype.fintype (fun j : ι => ¬ j ∈ s)
  let dI : D := ⟨i, hi⟩
  let βD := {d : D // d = dI}
  let restD := {d : D // ¬ d = dI}
  letI : Fintype βD := Subtype.fintype (fun d : D => d = dI)
  letI : Fintype restD := Subtype.fintype (fun d : D => ¬ d = dI)
  let erest : restD ≃ {j // ¬ j ∈ u} :=
    { toFun := fun d => ⟨d.1.1, by
        have hd_ne_i : d.1.1 ≠ i := by
          intro h
          apply d.2
          ext
          exact h
        have hd_not_s : d.1.1 ∉ s := d.1.2
        simp [u, Finset.mem_insert, hd_ne_i, hd_not_s]⟩
      invFun := fun c => ⟨⟨c.1, by
        have hc : ¬ c.1 ∈ u := c.2
        intro hs
        exact hc (by simp [u, hs])⟩, by
        intro h
        have : c.1 = i := by simpa [dI] using congrArg Subtype.val h
        have hc : ¬ c.1 ∈ u := c.2
        exact hc (by simp [u, this])⟩
      left_inv := by intro d; ext; rfl
      right_inv := by intro c; ext; rfl }
  set τs : Measure (∀ d : D, α d) := Measure.pi (fun d : D => μ d) with hτs
  set ρβD : Measure (∀ d : βD, α (d : D)) := Measure.pi (fun d : βD => μ (d : D)) with hρβD
  set τrest : Measure (∀ d : restD, α (d : D)) := Measure.pi (fun d : restD => μ (d : D)) with hτrest
  haveI : IsProbabilityMeasure τs := by
    rw [hτs]
    infer_instance
  haveI : IsProbabilityMeasure ρβD := by
    rw [hρβD]
    infer_instance
  haveI : IsProbabilityMeasure τrest := by
    rw [hτrest]
    infer_instance
  let eD0 := MeasurableEquiv.piEquivPiSubtypeProd (fun d : D => α d) (fun d : D => d = dI)
  let euD := MeasurableEquiv.piUnique (fun d : βD => α (d : D))
  let erestPi : (∀ d : restD, α (d : D)) ≃ᵐ (∀ c : {j // ¬ j ∈ u}, α c) :=
    MeasurableEquiv.piCongrLeft (fun c : {j // ¬ j ∈ u} => α c) erest
  let eD : (∀ d : D, α d) ≃ᵐ α i × (∀ c : {j // ¬ j ∈ u}, α c) :=
    eD0.trans (MeasurableEquiv.prodCongr euD erestPi)
  have hsplitD0 : MeasurePreserving eD0 τs (ρβD.prod τrest) := by
    rw [hτs, hρβD, hτrest]
    exact measurePreserving_piEquivPiSubtypeProd (fun d : D => μ d) (fun d : D => d = dI)
  have huniqD : MeasurePreserving euD ρβD (μ i) := by
    rw [hρβD]
    exact measurePreserving_piUnique (fun d : βD => μ (d : D))
  have hrestD : MeasurePreserving erestPi τrest τ := by
    rw [hτrest]
    change MeasurePreserving erestPi (Measure.pi (fun d : restD => μ (d : D)))
      (Measure.pi (fun c : {j // ¬ j ∈ u} => μ c))
    convert measurePreserving_piCongrLeft (fun c : {j // ¬ j ∈ u} => μ c) erest using 1 <;>
      rfl
  have hD : MeasurePreserving eD τs ((μ i).prod τ) := by
    exact ((huniqD.prod hrestD).comp hsplitD0)
  let eS : (∀ j, α j) ≃ᵐ (∀ j : s, α j) × (∀ d : D, α d) :=
    MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s)
  have mpS : MeasurePreserving eS (Measure.pi μ) (σ.prod τs) := by
    rw [hτs]
    convert measurePreserving_piEquivPiSubtypeProd μ (· ∈ s) using 2
    exact (measure_pi_eq_of_fintype _ _ (fun j : s => μ j)).symm
  set K : (∀ j : s, α j) → ℝ := fun y => ∫ x, G (x, y) ∂(μ i) with hK
  have hKint : Integrable K σ := by
    simpa [K, hK] using hGint.integral_prod_right
  have hcond_s_raw :
      (Measure.pi μ)[Z | F s] =ᵐ[Measure.pi μ]
        fun ω => ∫ z : (∀ d : D, α d),
          Z (eS.symm ((eS ω).1, z)) ∂τs := by
    exact condExp_piFinset_eq_marginal μ s hZint
  have heD_i :
      ∀ (x : α i) (d : ∀ c : {j // ¬ j ∈ u}, α c), eD.symm (x, d) dI = x := by
    intro x d
    simp [eD, eD0, euD, erestPi, erest, MeasurableEquiv.piEquivPiSubtypeProd,
      MeasurableEquiv.prodCongr, MeasurableEquiv.piUnique, MeasurableEquiv.piCongrLeft,
      Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piUnique_symm_apply, uniqueElim_default]
    have hdef : (⟨dI, rfl⟩ : βD) = default := Unique.eq_default _
    cases hdef
    exact (uniqueElim_default (α := fun d : βD => α (d : D)) x)
  have heD_rest :
      ∀ (x : α i) (d : ∀ c : {j // ¬ j ∈ u}, α c) (j : ι)
        (hjs : j ∉ s) (hju : j ∉ u),
        eD.symm (x, d) (⟨j, hjs⟩ : D) = d ⟨j, hju⟩ := by
    intro x d j hjs hju
    have hne : ¬ (⟨j, hjs⟩ : D) = dI := by
      intro h
      have hji : j = i := by simpa [dI] using congrArg Subtype.val h
      exact hju (by simp [u, hji])
    simp [eD, eD0, euD, erestPi, erest, hne, hju,
      MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.prodCongr,
      MeasurableEquiv.piUnique, MeasurableEquiv.piCongrLeft,
      Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piUnique_symm_apply,
      Equiv.piCongrLeft_symm_apply]
  have hcompat_s :
      ∀ (y : ∀ j : s, α j) (x : α i) (d : ∀ c : {j // ¬ j ∈ u}, α c),
        eS.symm (y, eD.symm (x, d)) = eFull ((x, y), d) := by
    intro y x d
    have heFull_i : eFull ((x, y), d) i = x := by
      have hmem_single : i ∈ singleton := by simp [singleton]
      have hmem_u : i ∈ u := by simp [u]
      have hmem_union : i ∈ singleton ∪ s := by simp [singleton]
      change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ u)).symm
          (eIS (x, y), d)) i = x
      rw [show ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ u)).symm
          (eIS (x, y), d)) i = eIS (x, y) ⟨i, hmem_u⟩ by
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hmem_u]]
      have hunion :
          (MeasurableEquiv.piFinsetUnion α hdisj) (eSing x, y) ⟨i, hmem_union⟩
            = eSing x ⟨i, hmem_single⟩ := by
        exact Equiv.piFinsetUnion_left α hdisj (f := eSing x) (g := y)
            hmem_single hmem_union
      have hsingle : eSing x ⟨i, hmem_single⟩ = x := by
        simp [eSing, singleton, MeasurableEquiv.piUnique, Equiv.piUnique_symm_apply,
          uniqueElim_default]
        have hdef : (⟨i, hmem_single⟩ : singleton) = default := Unique.eq_default _
        cases hdef
        exact (uniqueElim_default (α := fun j : singleton => α j) x)
      exact hunion.trans hsingle
    have heFull_s :
        ∀ (j : ι) (hjs : j ∈ s), eFull ((x, y), d) j = y ⟨j, hjs⟩ := by
      intro j hjs
      have hmem_u : j ∈ u := by simp [u, hjs]
      have hmem_union : j ∈ singleton ∪ s := by simp [singleton, hjs]
      change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ u)).symm
          (eIS (x, y), d)) j = y ⟨j, hjs⟩
      rw [show ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ u)).symm
          (eIS (x, y), d)) j = eIS (x, y) ⟨j, hmem_u⟩ by
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hmem_u]]
      have hunion :
          (MeasurableEquiv.piFinsetUnion α hdisj) (eSing x, y) ⟨j, hmem_union⟩
            = y ⟨j, hjs⟩ := by
        exact Equiv.piFinsetUnion_right α hdisj (f := eSing x) (g := y)
            hjs hmem_union
      exact hunion
    have heFull_rest :
        ∀ (j : ι) (hju : j ∉ u), eFull ((x, y), d) j = d ⟨j, hju⟩ := by
      intro j hju
      change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ u)).symm
          (eIS (x, y), d)) j = d ⟨j, hju⟩
      simp [MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, hju]
    ext j
    by_cases hjs : j ∈ s
    · calc
        eS.symm (y, eD.symm (x, d)) j = y ⟨j, hjs⟩ := by
          change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
              (y, eD.symm (x, d))) j = y ⟨j, hjs⟩
          simp [MeasurableEquiv.piEquivPiSubtypeProd,
            Equiv.piEquivPiSubtypeProd_symm_apply, hjs]
        _ = eFull ((x, y), d) j := (heFull_s j hjs).symm
    · by_cases hji : j = i
      · subst j
        calc
          eS.symm (y, eD.symm (x, d)) i = eD.symm (x, d) dI := by
            change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                (y, eD.symm (x, d))) i = eD.symm (x, d) dI
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hi, dI]
          _ = x := heD_i x d
          _ = eFull ((x, y), d) i := heFull_i.symm
      · have hju : j ∉ u := by simp [u, hji, hjs]
        calc
          eS.symm (y, eD.symm (x, d)) j = eD.symm (x, d) (⟨j, hjs⟩ : D) := by
            change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                (y, eD.symm (x, d))) j = eD.symm (x, d) (⟨j, hjs⟩ : D)
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hjs]
          _ = d ⟨j, hju⟩ := heD_rest x d j hjs hju
          _ = eFull ((x, y), d) j := (heFull_rest j hju).symm
  have hPermY :
      MeasurePreserving
        (fun q : (∀ j : s, α j) × (α i × (∀ c : {j // ¬ j ∈ u}, α c)) =>
          ((q.2.1, q.1), q.2.2))
        (σ.prod ((μ i).prod τ)) (((μ i).prod σ).prod τ) := by
    let f1 : (∀ j : s, α j) × (α i × (∀ c : {j // ¬ j ∈ u}, α c)) →
        ((∀ j : s, α j) × α i) × (∀ c : {j // ¬ j ∈ u}, α c) :=
      fun q => ((q.1, q.2.1), q.2.2)
    have hf1 : MeasurePreserving f1 (σ.prod ((μ i).prod τ)) ((σ.prod (μ i)).prod τ) := by
      exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc σ (μ i) τ)
    let f2 : ((∀ j : s, α j) × α i) × (∀ c : {j // ¬ j ∈ u}, α c) →
        (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c) :=
      fun q => ((q.1.2, q.1.1), q.2)
    have hf2 : MeasurePreserving f2 ((σ.prod (μ i)).prod τ) (((μ i).prod σ).prod τ) := by
      exact (Measure.measurePreserving_swap (μ := σ) (ν := μ i)).prod (MeasurePreserving.id τ)
    exact hf2.comp hf1
  have hfib_y_int :
      ∀ᵐ y ∂σ,
        Integrable (fun q : α i × (∀ c : {j // ¬ j ∈ u}, α c) => H ((q.1, y), q.2))
          ((μ i).prod τ) := by
    have hperm_int :
        Integrable
          (fun q : (∀ j : s, α j) × (α i × (∀ c : {j // ¬ j ∈ u}, α c)) =>
            H ((q.2.1, q.1), q.2.2))
          (σ.prod ((μ i).prod τ)) :=
      hPermY.integrable_comp_of_integrable hHint
    exact hperm_int.prod_right_ae
  have mpS_fst :
      MeasurePreserving (fun ω => (eS ω).1) (Measure.pi μ) σ :=
    measurePreserving_fst.comp mpS
  have hω_fib_int :
      ∀ᵐ ω ∂Measure.pi μ,
        Integrable
          (fun q : α i × (∀ c : {j // ¬ j ∈ u}, α c) => H ((q.1, (eS ω).1), q.2))
          ((μ i).prod τ) :=
    mpS_fst.quasiMeasurePreserving.tendsto_ae hfib_y_int
  have hcond_s :
      (Measure.pi μ)[Z | F s] =ᵐ[Measure.pi μ] fun ω => K (eS ω).1 := by
    refine hcond_s_raw.trans ?_
    filter_upwards [hω_fib_int] with ω hωint
    simp only [K, hK, G, hG]
    calc
      (∫ z : (∀ d : D, α d), Z (eS.symm ((eS ω).1, z)) ∂τs)
          = ∫ q : α i × (∀ c : {j // ¬ j ∈ u}, α c),
              Z (eS.symm ((eS ω).1, eD.symm q)) ∂((μ i).prod τ) := by
            let f : α i × (∀ c : {j // ¬ j ∈ u}, α c) → ℝ :=
              fun q => Z (eS.symm ((eS ω).1, eD.symm q))
            have hcomp :
                (fun z : (∀ d : D, α d) => Z (eS.symm ((eS ω).1, z)))
                  = fun z => f (eD z) := by
              ext z
              simp [f]
            rw [hcomp]
            exact hD.integral_comp' f
      _ = ∫ q : α i × (∀ c : {j // ¬ j ∈ u}, α c),
              H ((q.1, (eS ω).1), q.2) ∂((μ i).prod τ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
            simp [H, hcompat_s]
      _ = ∫ x, ∫ d, H ((x, (eS ω).1), d) ∂τ ∂(μ i) := by
            exact integral_prod _ hωint
      _ = ∫ x, (∫ d, H ((x, (eS ω).1), d) ∂τ) ∂(μ i) := rfl
  have hKfst_int :
      Integrable (fun q : (∀ j : s, α j) × (∀ d : D, α d) => K q.1) (σ.prod τs) :=
    hKint.comp_fst τs
  have hvarFs :
      Var[(Measure.pi μ)[Z | F s]; Measure.pi μ] = variance K σ := by
    calc
      Var[(Measure.pi μ)[Z | F s]; Measure.pi μ]
          = Var[(fun ω => K (eS ω).1); Measure.pi μ] := variance_congr hcond_s
      _ = Var[(fun q : (∀ j : s, α j) × (∀ d : D, α d) => K q.1); σ.prod τs] := by
            exact mpS.variance_fun_comp hKfst_int.aemeasurable
      _ = variance K σ := by
            exact measurePreserving_fst.variance_fun_comp hKint.aemeasurable
  have hdiff :
      (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
        = variance G ((μ i).prod σ) - variance K σ := by
    rw [hvarY, hvarFs] at hLOTV
    linarith
  have hupdate :
      ∀ (xi : α i) (y : ∀ j : s, α j) (d : ∀ c : {j // ¬ j ∈ u}, α c) (x : α i),
        Function.update (eFull ((xi, y), d)) i x = eFull ((x, y), d) := by
    intro xi y d x
    rw [← hcompat_s y xi d, ← hcompat_s y x d]
    ext j
    by_cases hjs : j ∈ s
    · have hji : j ≠ i := by
        intro h
        subst h
        exact hi hjs
      calc
        Function.update (eS.symm (y, eD.symm (xi, d))) i x j
            = eS.symm (y, eD.symm (xi, d)) j := by rw [Function.update_of_ne hji]
        _ = y ⟨j, hjs⟩ := by
            change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                (y, eD.symm (xi, d))) j = y ⟨j, hjs⟩
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hjs]
        _ = eS.symm (y, eD.symm (x, d)) j := by
            change y ⟨j, hjs⟩ =
              ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                (y, eD.symm (x, d))) j
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hjs]
    · by_cases hji : j = i
      · subst j
        calc
          Function.update (eS.symm (y, eD.symm (xi, d))) i x i = x := by
            rw [Function.update_self]
          _ = eD.symm (x, d) dI := (heD_i x d).symm
          _ = eS.symm (y, eD.symm (x, d)) i := by
            change eD.symm (x, d) dI =
              ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                (y, eD.symm (x, d))) i
            simp [MeasurableEquiv.piEquivPiSubtypeProd,
              Equiv.piEquivPiSubtypeProd_symm_apply, hi, dI]
      · have hju : j ∉ u := by simp [u, hji, hjs]
        calc
          Function.update (eS.symm (y, eD.symm (xi, d))) i x j
              = eS.symm (y, eD.symm (xi, d)) j := by rw [Function.update_of_ne hji]
          _ = eD.symm (xi, d) (⟨j, hjs⟩ : D) := by
              change ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                  (y, eD.symm (xi, d))) j = eD.symm (xi, d) (⟨j, hjs⟩ : D)
              simp [MeasurableEquiv.piEquivPiSubtypeProd,
                Equiv.piEquivPiSubtypeProd_symm_apply, hjs]
          _ = d ⟨j, hju⟩ := heD_rest xi d j hjs hju
          _ = eD.symm (x, d) (⟨j, hjs⟩ : D) := (heD_rest x d j hjs hju).symm
          _ = eS.symm (y, eD.symm (x, d)) j := by
              change eD.symm (x, d) (⟨j, hjs⟩ : D) =
                ((MeasurableEquiv.piEquivPiSubtypeProd α (fun j => j ∈ s)).symm
                  (y, eD.symm (x, d))) j
              simp [MeasurableEquiv.piEquivPiSubtypeProd,
                Equiv.piEquivPiSubtypeProd_symm_apply, hjs]
  set R : (∀ j : s, α j) × (∀ c : {j // ¬ j ∈ u}, α c) → ℝ :=
    fun yd => variance (fun x => H ((x, yd.1), yd.2)) (μ i) with hR
  have hAssocSymmR : MeasurePreserving
      (fun q : α i × ((∀ j : s, α j) × (∀ c : {j // ¬ j ∈ u}, α c)) =>
        ((q.1, q.2.1), q.2.2))
      ((μ i).prod (σ.prod τ)) (((μ i).prod σ).prod τ) := by
    exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (μ i) σ τ)
  have hH_by_x :
      MemLp
        (fun q : α i × ((∀ j : s, α j) × (∀ c : {j // ¬ j ∈ u}, α c)) =>
          H ((q.1, q.2.1), q.2.2))
        2 ((μ i).prod (σ.prod τ)) := by
    simpa [Function.comp_def] using hH.comp_measurePreserving hAssocSymmR
  have hRint_pair : Integrable R (σ.prod τ) := by
    simpa [R, hR] using integrable_variance_fiber_snd (μ i) (σ.prod τ) hH_by_x
  have hRint_y : Integrable (fun y => ∫ d, R (y, d) ∂τ) σ := by
    simpa using hRint_pair.integral_prod_left
  have hprojR :
      MeasurePreserving
        (fun q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c) =>
          (q.1.2, q.2))
        (((μ i).prod σ).prod τ) (σ.prod τ) := by
    exact (measurePreserving_snd : MeasurePreserving (Prod.snd : α i × (∀ j : s, α j) → (∀ j : s, α j))
        ((μ i).prod σ) σ).prod (MeasurePreserving.id τ)
  have hRprod_int :
      Integrable
        (fun q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c) => R (q.1.2, q.2))
        (((μ i).prod σ).prod τ) :=
    hprojR.integrable_comp_of_integrable hRint_pair
  have hRcomp_int :
      Integrable (fun p : α i × (∀ j : s, α j) => ∫ d, R (p.2, d) ∂τ) ((μ i).prod σ) :=
    hRint_y.comp_snd (μ i)
  have hprod_R :
      ∫ q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c),
          R (q.1.2, q.2) ∂(((μ i).prod σ).prod τ)
        = ∫ y, ∫ d, R (y, d) ∂τ ∂σ := by
    calc
      ∫ q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c),
          R (q.1.2, q.2) ∂(((μ i).prod σ).prod τ)
          = ∫ p : α i × (∀ j : s, α j), ∫ d, R (p.2, d) ∂τ ∂((μ i).prod σ) := by
            rw [integral_prod _ hRprod_int]
      _ = ∫ y, ∫ d, R (y, d) ∂τ ∂σ := by
            rw [integral_prod_symm _ hRcomp_int]
            simp
  have hRHS_transport :
      ∫ y, ∫ d, variance (fun x => H ((x, y), d)) (μ i) ∂τ ∂σ
        = ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
    let Vfull : (∀ j, α j) → ℝ :=
      fun ω => variance (fun x => Z (Function.update ω i x)) (μ i)
    have hcomp :
        (fun q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c) =>
          Vfull (eFull q))
          = fun q => R (q.1.2, q.2) := by
      ext q
      rcases q with ⟨⟨xi, y⟩, d⟩
      simp only [Vfull, R, hR]
      congr 1
      funext x
      simp [H, hupdate]
    calc
      ∫ y, ∫ d, variance (fun x => H ((x, y), d)) (μ i) ∂τ ∂σ
          = ∫ y, ∫ d, R (y, d) ∂τ ∂σ := by simp [R, hR]
      _ = ∫ q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c),
            R (q.1.2, q.2) ∂(((μ i).prod σ).prod τ) := hprod_R.symm
      _ = ∫ q : (α i × (∀ j : s, α j)) × (∀ c : {j // ¬ j ∈ u}, α c),
            Vfull (eFull q) ∂(((μ i).prod σ).prod τ) := by rw [hcomp]
      _ = ∫ ω, Vfull ω ∂(Measure.pi μ) := mpFull.integral_comp' Vfull
  change
    (Measure.pi μ)[Var[(Measure.pi μ)[Z | F u]; Measure.pi μ | F s]]
      ≤ ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ)
  rw [← hY]
  calc
    (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
        = variance G ((μ i).prod σ) - variance K σ := hdiff
    _ ≤ ∫ y, ∫ d, variance (fun x => H ((x, y), d)) (μ i) ∂τ ∂σ := by
          simpa [G, hG, K, hK] using hthree
    _ = ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) :=
          hRHS_transport


end ISec
