-- Prove2me | solution 1 for mme_block_tensor_is_matMul_kronPow_balanced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-07T15:01:17.575859+00:00
-- url     : https://prove2.me/submissions/17f09e68-c6a3-4865-b6ab-1713a2e061e1

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_tensor_rank

open MME

universe u

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t))
    (_hSym : MME.LaserSymmetric S)
    (_hsupport : TensorObj.LaserAlignedSupport G S)
    (N : ℕ)
    (induced : (T.kronPow N).TypeGrading (t ^ N))
    (σ : Fin 3 → Fin (t ^ N))
    (_hBalanced : ∀ k : Fin N,
        ((finFunctionFinEquiv (n := N) (m := t)).symm (σ 0) k,
         (finFunctionFinEquiv (n := N) (m := t)).symm (σ 1) k,
         (finFunctionFinEquiv (n := N) (m := t)).symm (σ 2) k) ∈ S) :
    ∃ (a b c : ℕ),
      TensorObj.Restrict
        (MMObj K a b c)
        (induced.blockSubtensor σ) := by
  refine ⟨0, 0, 0,
    fun _ => (0 : (induced.blockSubtensor σ).V _ →ₗ[K] (MMObj K 0 0 0).V _), ?_⟩
  have hRHS : (MMObj K 0 0 0).t = 0 := by
    show MMTensor K 0 0 0 = 0
    simp [MMTensor]
  have hmap :
      (PiTensorProduct.map
        (fun i : Fin 3 =>
          (0 : (induced.blockSubtensor σ).V i →ₗ[K] (MMObj K 0 0 0).V i))) = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    rw [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod]
    simp only [LinearMap.zero_apply]
    exact MultilinearMap.map_zero _
  rw [hmap, LinearMap.zero_apply, hRHS]
