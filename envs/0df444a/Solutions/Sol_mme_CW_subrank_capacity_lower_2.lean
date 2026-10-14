-- Prove2me | solution 2 for mme_CW_subrank_capacity_lower
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T14:34:38.234744+00:00
-- url     : https://prove2.me/submissions/863cb483-ee19-4ca1-87de-201ecaaba68e

import Mathlib.Tactic
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_subrank_capacity
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le
import Theorems.Thm_mme_HasTauValueAtLeast_mono_tau

open MME BigOperators PiTensorProduct
universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CWCapacity
variable {K : Type u} [Field K]

def select : Fin 3 → Fin 3 → Fin 8 :=
  ![![0,2,3], ![1,0,3], ![1,2,0]]

def project : ∀ s : Fin 3, CWSpace K 6 s →ₗ[K] (Fin 3 → K)
  | ⟨0, _⟩ =>
    { toFun := fun v j => v (select 0 j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | ⟨1, _⟩ =>
    { toFun := fun v j => v (select 1 j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | ⟨2, _⟩ =>
    { toFun := fun v j => v (select 2 j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem project_monom (a b c : Fin 8) :
    PiTensorProduct.map (project (K := K)) (CWMonom K 6 a b c) =
      tprod K (fun s : Fin 3 => fun j : Fin 3 =>
        if select s j = (![a,b,c] s) then (1:K) else 0) := by
  rw [CWMonom, PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;> ext j <;> simp [project, Pi.single_apply, eq_comm]

theorem cw_diag_three :
    TensorObj.Restrict (TensorObj.diagObj K 3 3) (CWObj K 6) := by
  refine ⟨project, ?_⟩
  change PiTensorProduct.map project (CWTensor K 6) =
    ∑ j : Fin 3, tprod K (fun _ : Fin 3 => Pi.single j (1:K))
  simp only [CWTensor, map_add, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, project_monom]
  have hvec (a b c : Fin 8) :
      (fun s : Fin 3 => fun j : Fin 3 =>
        if select s j = (![a,b,c] s) then (1:K) else 0) =
      ![(fun j => if select 0 j = a then (1:K) else 0),
        (fun j => if select 1 j = b then (1:K) else 0),
        (fun j => if select 2 j = c then (1:K) else 0)] := by
    funext s; fin_cases s <;> rfl
  simp only [hvec]
  have hfun (s : Fin 3) (a : Fin 8) :
      (fun j : Fin 3 => if select s j = a then (1:K) else 0) =
        ![if select s 0 = a then 1 else 0,
          if select s 1 = a then 1 else 0,
          if select s 2 = a then 1 else 0] := by
    ext j; fin_cases j <;> rfl
  simp only [hfun]
  norm_num [select, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk, Fin.ext_iff] 

  have hz : (![0,0,0] : Fin 3 → K) = 0 := by ext j; fin_cases j <;> rfl
  have ht0 (v w : Fin 3 → K) : tprod K ![0,v,w] = 0 :=
    MultilinearMap.map_coord_zero _ (0 : Fin 3) rfl
  have ht1 (v w : Fin 3 → K) : tprod K ![v,0,w] = 0 :=
    MultilinearMap.map_coord_zero _ (1 : Fin 3) rfl
  have ht2 (v w : Fin 3 → K) : tprod K ![v,w,0] = 0 :=
    MultilinearMap.map_coord_zero _ (2 : Fin 3) rfl
  have hd (v : Fin 3 → K) : ![v,v,v] = (fun _ : Fin 3 => v) := by
    ext j; fin_cases j <;> rfl
  have hb0 : (![1,0,0] : Fin 3 → K) = Pi.single 0 1 := by
    ext j; fin_cases j <;> simp [Fin.ext_iff]
  have hb1 : (![0,1,0] : Fin 3 → K) = Pi.single 1 1 := by
    ext j; fin_cases j <;> simp [Fin.ext_iff]
  have hb2 : (![0,0,1] : Fin 3 → K) = Pi.single 2 1 := by
    ext j; fin_cases j <;> simp [Fin.ext_iff]
  simp only [hz, ht0, ht1, ht2, zero_add, add_zero, hd, hb0, hb1, hb2]

theorem scalar_extraction (N : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (3^N) => MMObj K 1 1 1))
      ((CWObj K 6).kronPow N) := by
  let P := tensorPreorder K
  have hb : P.le (3 : TensorQ K 3) (TensorQ.toQ (CWObj K 6)) :=
    cw_diag_three
  have hp : ∀ n : ℕ, P.le ((3 : TensorQ K 3)^n)
      ((TensorQ.toQ (CWObj K 6))^n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using P.le_refl (1 : TensorQ K 3)
    | succ n ih =>
      rw [pow_succ, pow_succ]
      apply P.le_trans _ _ _ (P.mul_right _ _ ih 3)
      rw [mul_comm _ 3, mul_comm _ (TensorQ.toQ (CWObj K 6))]
      exact P.mul_right _ _ hb _
  have he : TensorQ.toQ
      (TensorObj.bigAdd (fun _ : Fin (3^N) => MMObj K 1 1 1)) =
        (3 : TensorQ K 3)^N := by
    rw [TensorQ.toQ_bigAdd]
    change (∑ _ : Fin (3^N), MMq K 1 1 1) = _
    simp [MMq_one, -TensorQ.toQ_one]
  change P.le (TensorQ.toQ _) (TensorQ.toQ _)
  rw [he, TensorQ.toQ_kronPow]
  exact hp N

theorem capacity_ge_of_value (T : TensorObj K 3) (V : ℝ) (hV : 1 ≤ V)
    (h : HasTauValueAtLeast T (1/3) V) : V ≤ subrankCapacity T := by
  unfold subrankCapacity
  refine le_csSup ?_ ⟨hV,h.2⟩
  refine ⟨max 0 (tensorAsymptoticRank T), ?_⟩
  rintro W ⟨hW,hw⟩
  apply mme_tau_value_le_of_asymptoticRank_le (le_max_left _ _) hW (le_max_right _ _)
  apply mme_HasTauValueAtLeast_mono_tau (by norm_num : (0:ℝ)<1/3) ?_ ⟨by linarith,hw⟩
  have := one_le_matMulExp_strassen (K := K)
  linarith

theorem cw_value_three : HasTauValueAtLeast (CWObj K 6) (1/3) 3 := by
  refine ⟨by norm_num, ?_⟩
  intro ε hε
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro N
  refine ⟨3^N, fun _ => 1, fun _ => 1, fun _ => 1, scalar_extraction N, ?_⟩
  simp only [mul_one, Nat.cast_one, Real.one_rpow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤3) N]

end CWCapacity

theorem solution {K : Type u} [Field K] :
    (5 : ℝ)/2 ≤ subrankCapacity (CWObj K 6) := by
  have h := CWCapacity.capacity_ge_of_value (CWObj K 6) 3 (by norm_num)
    CWCapacity.cw_value_three
  linarith
