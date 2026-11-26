-- Prove2me | solution 1 for section5_tensor_synthesis_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:24.838472+00:00
-- url     : https://prove2.me/submissions/8ce62a3c-ca76-4599-8838-c407efe00d81

import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_l2_add_bound
import Theorems.Thm_section5_product_synthesis_bound
import Theorems.Thm_section5_tensor_synthesis_bound
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/









theorem section5_memLp_product_synthesis {α β ι κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Fintype ι] [Fintype κ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (f : ι → α → ℂ) (g : κ → β → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ j, MemLp (g j) 2 ν) (c : ι → κ → ℂ) :
    MemLp (fun z : α×β => ∑ i, ∑ j, c i j*f i z.1*g j z.2) 2 (μ.prod ν) := by
  apply memLp_finsetSum _ (fun i _ => ?_)
  apply memLp_finsetSum _ (fun j _ => ?_)
  exact section5_memLp_product (fun x => c i j*f i x) (g j) ((hf i).const_mul _) (hg j)







theorem section5_synthesis_add_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f g : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : section5_SynthesisBound μ f A) (hgb : section5_SynthesisBound μ g B) :
    section5_SynthesisBound μ (fun i x => f i x+g i x) (A+B) := by
  intro c
  simpa only [mul_add,Finset.sum_add_distrib] using
    section5_l2_add_bound _ _ (section5_memLp_synthesis f hf c)
    (section5_memLp_synthesis g hg c) A B _ hA hB
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (hfa c) (hgb c)

theorem section5_product_synthesis_error {α β ι κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Fintype ι] [Fintype κ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (f g : ι → α → ℂ) (f' g' : κ → β → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hf' : ∀ j, MemLp (f' j) 2 ν) (hg' : ∀ j, MemLp (g' j) 2 ν)
    (A B δ δ' : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hfa : section5_SynthesisBound ν f' A) (hgb : section5_SynthesisBound μ g B)
    (hfg : section5_SynthesisBound μ (fun i x => f i x-g i x) δ)
    (hfg' : section5_SynthesisBound ν (fun j y => f' j y-g' j y) δ')
    (c : ι → κ → ℂ) :
    (∫ z : α×β,
      ‖(∑ i, ∑ j, c i j*f i z.1*f' j z.2)-
        (∑ i, ∑ j, c i j*g i z.1*g' j z.2)‖^2 ∂(μ.prod ν)) ≤
      (δ*A+B*δ')^2*∑ i, ∑ j, ‖c i j‖^2 := by
  let H₁ := fun z : α×β => ∑ i, ∑ j, c i j*(f i z.1-g i z.1)*f' j z.2
  let H₂ := fun z : α×β => ∑ i, ∑ j, c i j*g i z.1*(f' j z.2-g' j z.2)
  have hi₁ : MemLp H₁ 2 (μ.prod ν) :=
    section5_memLp_product_synthesis _ f' (fun i => (hf i).sub (hg i)) hf' c
  have hi₂ : MemLp H₂ 2 (μ.prod ν) :=
    section5_memLp_product_synthesis g _ hg (fun j => (hf' j).sub (hg' j)) c
  have hb₁ := section5_product_synthesis_bound _ f'
    (fun i => (hf i).sub (hg i)) hf' δ A hfg hfa c
  have hb₂ := section5_product_synthesis_bound g _ hg
    (fun j => (hf' j).sub (hg' j)) B δ' hgb hfg' c
  have heq : (fun z : α×β => (∑ i, ∑ j, c i j*f i z.1*f' j z.2)-
        (∑ i, ∑ j, c i j*g i z.1*g' j z.2)) = fun z => H₁ z+H₂ z := by
    funext z
    dsimp only [H₁,H₂]
    rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have heq' (z : α×β) : (∑ i, ∑ j, c i j*f i z.1*f' j z.2)-
      (∑ i, ∑ j, c i j*g i z.1*g' j z.2) = H₁ z+H₂ z := congrFun heq z
  simp_rw [heq']
  exact section5_l2_add_bound H₁ H₂ hi₁ hi₂ (δ*A) (B*δ') _
    (mul_nonneg hδ hA) (mul_nonneg hB hδ')
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) hb₁ hb₂



theorem section5_sum_tuple_succ {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (n : ℕ) (F : (Fin (n+1) → ι) → R) :
    (∑ a, F a) = ∑ i, ∑ a : Fin n → ι, F (Fin.cons i a) := by
  calc
    _ = ∑ p : ι×(Fin n → ι), F (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => ι))
        (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _



theorem section5_integral_pi_succ {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (n : ℕ) (F : (Fin (n+1) → α) → ℝ) :
    (∫ x, F x ∂(Measure.pi (fun _ : Fin (n+1) => μ))) =
      ∫ z : α×(Fin n → α), F (Fin.cons z.1 z.2) ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) 0).symm
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  have h := hmp.integral_comp e.measurableEmbedding F
  simpa [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h.symm



theorem section5_synthesis_sub_swap {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f g : ι → α → ℂ) (δ : ℝ)
    (h : section5_SynthesisBound μ (fun i x => f i x-g i x) δ) :
    section5_SynthesisBound μ (fun i x => g i x-f i x) δ := by
  intro c
  calc
    _ = ∫ x, ‖∑ i, c i*(f i x-g i x)‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [mul_sub,Finset.sum_sub_distrib]
      rw [norm_sub_rev]
    _ ≤ _ := h c

theorem section5_synthesis_perturb_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f g : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hfa : section5_SynthesisBound μ f 1)
    (hfg : section5_SynthesisBound μ (fun i x => f i x-g i x) δ) :
    section5_SynthesisBound μ g (1+δ) := by
  have h := section5_synthesis_add_bound f (fun i x => g i x-f i x) hf
    (fun i => (hg i).sub (hf i)) 1 δ (by norm_num) hδ hfa
    (section5_synthesis_sub_swap f g δ hfg)
  have heq : (fun i x => f i x+(g i x-f i x)) = g := by funext i x; ring
  rwa [heq] at h















end
set_option autoImplicit false
open MeasureTheory

theorem solution {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [SigmaFinite μ] (f g : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hfa : section5_SynthesisBound μ f 1)
    (hfg : section5_SynthesisBound μ (fun i x => f i x-g i x) δ) (n : ℕ) :
    section5_SynthesisBound (Measure.pi (fun _ : Fin n => μ))
      (fun a x => section5_tensor_family f n a x-section5_tensor_family g n a x)
      ((1+δ)^n-1) := by
  have hgb := section5_synthesis_perturb_bound f g hf hg δ hδ hfa hfg
  induction n with
  | zero => intro c; simp [section5_tensor_family]
  | succ n ih =>
    intro c
    have hpow : 0 ≤ (1+δ)^n-1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
    have hfa' : section5_SynthesisBound (Measure.pi (fun _ : Fin n => μ))
        (section5_tensor_family f n) 1 := by
      simpa only [one_pow] using section5_tensor_synthesis_bound μ f hf 1 hfa n
    have h := section5_product_synthesis_error f g (section5_tensor_family f n)
      (section5_tensor_family g n) hf hg (section5_tensor_family_memLp μ f hf n)
      (section5_tensor_family_memLp μ g hg n) 1 (1+δ) δ ((1+δ)^n-1)
      (by norm_num) (by linarith) hδ hpow hfa' hgb hfg ih (fun i a => c (Fin.cons i a))
    have hrec : δ*1+(1+δ)*((1+δ)^n-1) = (1+δ)^(n+1)-1 := by rw [pow_succ]; ring
    rw [hrec] at h
    rw [section5_integral_pi_succ μ n]
    simp_rw [section5_sum_tuple_succ n]
    simpa only [section5_tensor_family,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
      mul_sub,Finset.sum_sub_distrib,mul_assoc] using h
