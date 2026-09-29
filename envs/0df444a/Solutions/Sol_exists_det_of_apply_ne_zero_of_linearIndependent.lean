-- Prove2me | solution 1 for exists_det_of_apply_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8a593866-62a3-502a-91a2-4516b06dcad5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_det_of_apply_ne_zero_of_linearIndependent

set_option autoImplicit false

namespace KcUnisolvence

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {X : Type*}

theorem det_eval_snoc {n : ℕ} (f : Fin (n + 1) → X → 𝕜) (x' : Fin n → X) (y : X) :
    (Matrix.of fun i j : Fin (n + 1) => f j (Fin.snoc (α := fun _ => X) x' y i)).det =
      ∑ j : Fin (n + 1), ((-1 : 𝕜) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
        (Matrix.of fun i k : Fin n => f (j.succAbove k) (x' i)).det) * f j y := by
  rw [Matrix.det_succ_row _ (Fin.last n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Matrix.of fun i j : Fin (n + 1) => f j (Fin.snoc (α := fun _ => X) x' y i)) (Fin.last n) j = f j y := by
    simp [Matrix.of_apply, Fin.snoc_last]
  have h2 : (Matrix.of fun i j : Fin (n + 1) => f j (Fin.snoc (α := fun _ => X) x' y i)).submatrix (Fin.last n).succAbove j.succAbove =
      Matrix.of fun i k : Fin n => f (j.succAbove k) (x' i) := by
    ext i k
    simp [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.snoc_castSucc]
  rw [h1, h2]
  ring

theorem exists_det_ne_zero :
    ∀ {n : ℕ} (f : Fin n → X → 𝕜), LinearIndependent 𝕜 f →
      ∃ x : Fin n → X, (Matrix.of fun i j : Fin n => f j (x i)).det ≠ 0
  | 0, f, _ => ⟨Fin.elim0, by simp [Matrix.det_fin_zero]⟩
  | n + 1, f, hf => by
    have hf' : LinearIndependent 𝕜 (fun j : Fin n => f (Fin.castSucc j)) :=
      hf.comp _ (Fin.castSucc_injective n)
    obtain ⟨x', hx'⟩ := exists_det_ne_zero (fun j : Fin n => f (Fin.castSucc j)) hf'

    let c : Fin (n + 1) → 𝕜 := fun j => (-1 : 𝕜) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
      (Matrix.of fun i k : Fin n => f (j.succAbove k) (x' i)).det
    have hclast : c (Fin.last n) ≠ 0 := by
      show (-1 : 𝕜) ^ ((Fin.last n : ℕ) + ((Fin.last n : Fin (n + 1)) : ℕ)) *
        (Matrix.of fun i k : Fin n => f ((Fin.last n).succAbove k) (x' i)).det ≠ 0
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ?_
      simpa only [Fin.succAbove_last] using hx'
    by_contra hall
    push Not at hall

    have hsum : ∑ j : Fin (n + 1), c j • f j = 0 := by
      funext y
      have := hall (Fin.snoc (α := fun _ => X) x' y)
      rw [det_eval_snoc] at this
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    exact hclast (Fintype.linearIndependent_iff.1 hf c hsum (Fin.last n))

theorem exists_det_ne_zero_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → X → 𝕜)
    (hf : LinearIndependent 𝕜 f) :
    ∃ x : ι → X, (Matrix.of fun i j : ι => f j (x i)).det ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hf' : LinearIndependent 𝕜 (fun k : Fin (Fintype.card ι) => f (e.symm k)) :=
    hf.comp _ e.symm.injective
  obtain ⟨x, hx⟩ := exists_det_ne_zero (fun k : Fin (Fintype.card ι) => f (e.symm k)) hf'
  refine ⟨fun i => x (e i), ?_⟩
  have h : (Matrix.of fun i j : ι => f j (x (e i))) =
      (Matrix.of fun k l : Fin (Fintype.card ι) => f (e.symm l) (x k)).submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply]
  rw [h, Matrix.det_submatrix_equiv_self]
  exact hx

end KcUnisolvence

theorem solution
    {𝕜 : Type*} [Field 𝕜] {X : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → 𝕜) (hf : LinearIndependent 𝕜 f) :
    ∃ x : ι → X, (Matrix.of fun i j : ι => f j (x i)).det ≠ 0 :=
  KcUnisolvence.exists_det_ne_zero_fintype f hf

end S_exists_det_of_apply_ne_zero_of_linearIndependent
end P2MW
export P2MW.S_exists_det_of_apply_ne_zero_of_linearIndependent (solution)
