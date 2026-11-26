-- Prove2me | solution 1 for section5_product_synthesis_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:26.326525+00:00
-- url     : https://prove2.me/submissions/8d292206-064b-498a-881c-955b2979a864

import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
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







































end
set_option autoImplicit false
open MeasureTheory

theorem solution {α β ι κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Fintype ι] [Fintype κ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (f : ι → α → ℂ) (g : κ → β → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ j, MemLp (g j) 2 ν)
    (A B : ℝ)
    (hA : ∀ c : ι → ℂ, (∫ x, ‖∑ i, c i*f i x‖^2 ∂μ) ≤ A^2*∑ i, ‖c i‖^2)
    (hB : ∀ c : κ → ℂ, (∫ y, ‖∑ j, c j*g j y‖^2 ∂ν) ≤ B^2*∑ j, ‖c j‖^2)
    (c : ι → κ → ℂ) :
    (∫ z : α×β, ‖∑ i, ∑ j, c i j*f i z.1*g j z.2‖^2 ∂(μ.prod ν)) ≤
      (A*B)^2*∑ i, ∑ j, ‖c i j‖^2 := by
  let H := fun z : α×β => ∑ i, ∑ j, c i j*f i z.1*g j z.2
  let d := fun (i : ι) (y : β) => ∑ j, c i j*g j y
  have hH := (section5_memLp_product_synthesis f g hf hg c).norm.integrable_sq
  change Integrable (fun z => ‖H z‖^2) (μ.prod ν) at hH
  have hd (i : ι) : MemLp (d i) 2 ν := section5_memLp_synthesis g hg (c i)
  have hboundint : Integrable (fun y => A^2*∑ i, ‖d i y‖^2) ν :=
    (integrable_finsetSum _ (fun i _ => (hd i).norm.integrable_sq)).const_mul _
  have hrepr (x : α) (y : β) : H (x,y) = ∑ i, d i y*f i x := by
    dsimp only [H,d]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    _ = ∫ y, ∫ x, ‖H (x,y)‖^2 ∂μ ∂ν := integral_prod_symm _ hH
    _ ≤ ∫ y, A^2*∑ i, ‖d i y‖^2 ∂ν := by
      apply integral_mono hH.integral_prod_right hboundint
      intro y
      simp_rw [hrepr]
      exact hA (fun i => d i y)
    _ = A^2*∑ i, ∫ y, ‖d i y‖^2 ∂ν := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hd i).norm.integrable_sq)]
    _ ≤ A^2*∑ i, B^2*∑ j, ‖c i j‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      exact Finset.sum_le_sum (fun i _ => hB (c i))
    _ = _ := by rw [← Finset.mul_sum]; ring
