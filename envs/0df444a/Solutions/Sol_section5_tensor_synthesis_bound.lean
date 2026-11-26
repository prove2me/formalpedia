-- Prove2me | solution 1 for section5_tensor_synthesis_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:59.551154+00:00
-- url     : https://prove2.me/submissions/591f62be-2eef-4061-ab81-504ad9aa3735

import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_product_synthesis_bound
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/























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





















end
set_option autoImplicit false
open MeasureTheory
theorem solution {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [SigmaFinite μ] (f : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (A : ℝ) (hA : section5_SynthesisBound μ f A) (n : ℕ) :
    section5_SynthesisBound (Measure.pi (fun _ : Fin n => μ)) (section5_tensor_family f n) (A^n) := by
  induction n with
  | zero =>
    intro c
    let a₀ : Fin 0 → ι := Fin.elim0
    haveI : Unique (Fin 0 → ι) := ⟨⟨a₀⟩,fun a => by funext i; exact Fin.elim0 i⟩
    haveI : ∀ i : Fin 0, IsProbabilityMeasure ((fun _ : Fin 0 => μ) i) := fun i => Fin.elim0 i
    simp [section5_tensor_family]
  | succ n ih =>
    intro c
    have h := section5_product_synthesis_bound f (section5_tensor_family f n) hf
      (section5_tensor_family_memLp μ f hf n) A (A^n) hA ih (fun i a => c (Fin.cons i a))
    have hp : A*A^n = A^(n+1) := by rw [pow_succ]; ring
    rw [hp] at h
    rw [section5_integral_pi_succ μ n]
    simp_rw [section5_sum_tuple_succ n]
    simpa only [section5_tensor_family,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
      mul_assoc] using h
