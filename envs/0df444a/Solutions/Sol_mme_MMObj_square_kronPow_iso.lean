-- Prove2me | solution 1 for mme_MMObj_square_kronPow_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:32:21.4214+00:00
-- url     : https://prove2.me/submissions/703fe55e-986a-409e-ace5-d80ccf2c8aca

import Definitions.Def_mme_omega_normalize

open MME PiTensorProduct

universe u

namespace MMObjSquareKronPowIso

private noncomputable def mmPure
    (K : Type u) [Field K] (n m p : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

private theorem mmobj_t_eq
    {K : Type u} [Field K] (n m p : ℕ) :
    (MMObj K n m p).t =
      ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, mmPure K n m p i j k := rfl

theorem one_iso
    {K : Type u} [Field K] :
    TensorObj.Isomorphic (TensorObj.oneObj : TensorObj K 3)
      (MMObj K 1 1 1) := by
  let toMM : ∀ s : Fin 3,
      (TensorObj.oneObj : TensorObj K 3).V s →ₗ[K] (MMObj K 1 1 1).V s :=
    fun s => Fin.cases
      (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
      (fun s => Fin.cases
        (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
        (fun s => Fin.cases
          (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
          (fun s => absurd s.isLt (by omega)) s) s) s
  let toOne : ∀ s : Fin 3,
      (MMObj K 1 1 1).V s →ₗ[K] (TensorObj.oneObj : TensorObj K 3).V s :=
    fun s => Fin.cases (LinearMap.proj (0, 0))
      (fun s => Fin.cases (LinearMap.proj (0, 0))
        (fun s => Fin.cases (LinearMap.proj (0, 0))
          (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨?_, ?_⟩
  · refine ⟨toOne, ?_⟩
    show PiTensorProduct.map _ (MMObj K 1 1 1).t =
      (TensorObj.oneObj : TensorObj K 3).t
    rw [mmobj_t_eq, Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
    show PiTensorProduct.map toOne (mmPure K 1 1 1 0 0 0) =
      tprod K (fun _ => (1 : K))
    simp only [mmPure]
    erw [PiTensorProduct.map_tprod]
    congr 1
    funext s
    fin_cases s <;>
      · change (LinearMap.proj (0, 0))
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) = 1
        rw [LinearMap.proj_apply, Pi.single_eq_same]
  · refine ⟨toMM, ?_⟩
    show PiTensorProduct.map _ (TensorObj.oneObj : TensorObj K 3).t =
      (MMObj K 1 1 1).t
    show PiTensorProduct.map toMM (tprod K (fun _ => (1 : K))) =
      (MMObj K 1 1 1).t
    rw [mmobj_t_eq, Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
    show _ = mmPure K 1 1 1 0 0 0
    simp only [mmPure]
    erw [PiTensorProduct.map_tprod]
    congr 1
    funext s
    fin_cases s <;>
      · change LinearMap.smulRight (1 : K →ₗ[K] K)
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) (1 : K) =
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        simp [LinearMap.smulRight_apply]

end MMObjSquareKronPowIso

theorem solution
    {K : Type u} [Field K] (n k : ℕ) :
    TensorObj.Isomorphic (TensorObj.kronPow (MMObj K n n n) k)
      (MMObj K (n ^ k) (n ^ k) (n ^ k)) := by
  induction k with
  | zero => exact MMObjSquareKronPowIso.one_iso
  | succ j ih =>
    change TensorObj.Isomorphic
      (TensorObj.kron (MMObj K n n n)
        (TensorObj.kronPow (MMObj K n n n) j))
      (MMObj K (n ^ (j + 1)) (n ^ (j + 1)) (n ^ (j + 1)))
    have hkron : TensorObj.Isomorphic
        (TensorObj.kron (MMObj K n n n)
          (TensorObj.kronPow (MMObj K n n n) j))
        (TensorObj.kron (MMObj K n n n)
          (MMObj K (n ^ j) (n ^ j) (n ^ j))) :=
      TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _) ih
    refine hkron.trans ?_
    have hmul := MMObj_kron_iso (K := K)
      n n n (n ^ j) (n ^ j) (n ^ j)
    rw [show n * n ^ j = n ^ (j + 1) from by
      rw [pow_succ]
      exact Nat.mul_comm _ _] at hmul
    exact hmul
