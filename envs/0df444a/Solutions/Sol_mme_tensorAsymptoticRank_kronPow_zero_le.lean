-- Prove2me | solution 1 for mme_tensorAsymptoticRank_kronPow_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:24:12.743949+00:00
-- url     : https://prove2.me/submissions/dbf8392e-fac8-49fb-bdd5-c567b8440779

import Definitions.Def_mme_tensor_rank

open MME PiTensorProduct BigOperators

universe u


namespace CWKronPowZero

variable {K : Type u} [Field K] {d : ℕ}

private theorem interchange_tprod
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem restrict_diag_one_of_pure
    (Z : TensorObj K d) (z : ∀ i, Z.V i)
    (hZ : Z.t = tprod K z) :
    TensorObj.Restrict Z (TensorObj.diagObj K d 1) := by
  let f : ∀ i, (Fin 1 → K) →ₗ[K] Z.V i := fun i =>
    LinearMap.smulRight (LinearMap.proj (0 : Fin 1)) (z i)
  refine ⟨f, ?_⟩
  show PiTensorProduct.map f
      (∑ j : Fin 1, tprod K (fun _ => (Pi.single j 1 : Fin 1 → K))) = Z.t
  rw [hZ, Fin.sum_univ_one, PiTensorProduct.map_tprod]
  congr 1
  funext i
  simp [f, LinearMap.smulRight_apply]

private theorem one_pow_one_rank_le :
    tensorRankObj ((TensorObj.oneObj : TensorObj K d).kronPow 1) ≤ 1 := by
  apply Nat.sInf_le
  apply restrict_diag_one_of_pure
    ((TensorObj.oneObj : TensorObj K d).kronPow 1)
    (fun _ => (1 : K) ⊗ₜ[K] (1 : K))
  change interchange (tprod K (fun _ : Fin d => (1 : K)))
      (tprod K (fun _ : Fin d => (1 : K))) = _
  exact interchange_tprod (fun _ : Fin d => (1 : K))
    (fun _ : Fin d => (1 : K))

private theorem one_asymptoticRank_le :
    tensorAsymptoticRank (TensorObj.oneObj : TensorObj K d) ≤ 1 := by
  rw [tensorAsymptoticRank]
  let a : ℕ → ℝ := fun n =>
    (tensorRankObj ((TensorObj.oneObj : TensorObj K d).kronPow (n + 1)) : ℝ) ^
      ((1 : ℝ) / (n + 1))
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    (⨅ n : ℕ, a n) ≤ a 0 := ciInf_le hbdd 0
    _ = (tensorRankObj ((TensorObj.oneObj : TensorObj K d).kronPow 1) : ℝ) := by
      simp [a]
    _ ≤ 1 := by exact_mod_cast one_pow_one_rank_le (K := K) (d := d)

end CWKronPowZero


theorem solution
    {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) :
    tensorAsymptoticRank (X.kronPow 0) ≤ tensorAsymptoticRank X ^ 0 := by
  change tensorAsymptoticRank (TensorObj.oneObj : TensorObj K d) ≤ 1
  exact CWKronPowZero.one_asymptoticRank_le
