-- Prove2me | solution 1 for mme_block_tensor_is_matMul_refined
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T12:09:16.156379+00:00
-- url     : https://prove2.me/submissions/b674754d-d619-4961-b2ec-ae82e29cf818

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_tensor_rank
open MME

set_option autoImplicit false

open PiTensorProduct in
/-- The matrix-multiplication tensor `⟨a,b,c⟩` is nonzero whenever `a, b, c ≥ 1`:
the coordinate functional at the entries `(0,0)`, `(0,0)`, `(0,0)` evaluates to `1`. -/
theorem MMTensor_ne_zero_aux {K : Type} [Field K] (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MMTensor K a b c ≠ 0 := by
  let i0 : Fin a := ⟨0, ha⟩
  let j0 : Fin b := ⟨0, hb⟩
  let k0 : Fin c := ⟨0, hc⟩
  let ev : ∀ i : Fin 3, MMSpace K a b c i →ₗ[K] K := fun i =>
    match i with
    | ⟨0, _⟩ => LinearMap.proj (i0, j0)
    | ⟨1, _⟩ => LinearMap.proj (j0, k0)
    | ⟨2, _⟩ => LinearMap.proj (k0, i0)
  let φ : PiTensorProduct K (MMSpace K a b c) →ₗ[K] K :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K (Fin 3) K).compLinearMap ev)
  intro h
  have key : φ (MMTensor K a b c) = 1 := by
    simp only [MMTensor, map_sum, φ, PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three]
    simp only [ev, LinearMap.proj_apply, Pi.single_apply]
    rw [Fintype.sum_eq_single i0, Fintype.sum_eq_single j0, Fintype.sum_eq_single k0]
    · simp
    · intro z hz; simp [Ne.symm hz]
    · intro y hy; exact Finset.sum_eq_zero fun z _ => by simp [Ne.symm hy]
    · intro x hx
      exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => by simp [Ne.symm hx]
  rw [h, map_zero] at key
  exact zero_ne_one key

/-- The zero tensor with three one-dimensional mode spaces. -/
noncomputable def ZeroT : TensorObj ℚ 3 := { V := fun _ => ℚ, t := 0 }

/-- The trivial one-class grading of `ZeroT`. -/
noncomputable def ZeroG : ZeroT.TypeGrading 1 where
  decomp := fun _ _ => ⊤
  is_internal := fun _ => by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep_subsingleton _
    · simp

theorem solution : ¬ (∀ {K : Type} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t)
    (S : Finset (Fin t × Fin t × Fin t)) (_hsupport : TensorObj.LaserAlignedSupport G S)
    (σ : Fin 3 → Fin t) (_hσ : (σ 0, σ 1, σ 2) ∈ S),
    TensorObj.Restrict (MMObj K (Module.finrank K (G.classOf 0 (σ 0) : Submodule K (T.V 0)))
      (Module.finrank K (G.classOf 1 (σ 1) : Submodule K (T.V 1)))
      (Module.finrank K (G.classOf 2 (σ 2) : Submodule K (T.V 2)))) (G.blockSubtensor σ)) := by
  intro h
  have hsupport : TensorObj.LaserAlignedSupport ZeroG ({((0 : Fin 1), (0 : Fin 1), (0 : Fin 1))} : Finset _) :=
    ⟨0, Fin.elim0, Fin.elim0, (Fin.sum_univ_zero _).symm, fun j => j.elim0⟩
  have hres := h ZeroG _ hsupport (fun _ => 0) (by simp)
  have key : ∀ a b c : ℕ, a = 1 → b = 1 → c = 1 →
      ¬ TensorObj.Restrict (MMObj ℚ a b c) (ZeroG.blockSubtensor (fun _ => 0)) := by
    rintro a b c rfl rfl rfl ⟨f, hf⟩
    have h0 : (ZeroG.blockSubtensor (fun _ => 0)).t = 0 := by
      show PiTensorProduct.map _ ZeroT.t = 0
      exact map_zero _
    rw [h0, map_zero] at hf
    exact MMTensor_ne_zero_aux 1 1 1 one_pos one_pos one_pos hf.symm
  refine key _ _ _ ?_ ?_ ?_ hres <;>
    exact (finrank_top ℚ ℚ).trans (Module.finrank_self ℚ)
