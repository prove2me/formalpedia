-- Prove2me | solution 1 for mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:54:35.121749+00:00
-- url     : https://prove2.me/submissions/51c78329-a354-4109-a171-a7f29a69b7f1

import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d t : ℕ}
    {T : TensorObj K d}
    (G : T.TypeGrading t)
    {Index : Fin d → Type u}
    [∀ i, Fintype (Index i)] [∀ i, DecidableEq (Index i)]
    (b : ∀ i, Basis (Index i) K (T.V i))
    (grade : ∀ i, Index i → Fin t)
    (hhomogeneous : ∀ i x,
      b i x ∈ G.classOf i (grade i x))
    (selected : ∀ i, Index i)
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (maps : ∀ i, T.V i →ₗ[K] W i)
    (hsupported : ∀ i x, x ≠ selected i → maps i (b i x) = 0)
    (hzero : G.blockTensor (fun i ↦ grade i (selected i)) = 0) :
    PiTensorProduct.map maps T.t = 0 := by
  let blockMaps : ∀ i : Fin d,
      G.classOf i (grade i (selected i)) →ₗ[K] W i := fun i ↦
    (maps i).comp (G.classOf i (grade i (selected i))).subtype
  have hfactor : ∀ i, maps i =
      (blockMaps i).comp (G.blockProj i (grade i (selected i))) := by
    intro i
    apply (b i).ext
    intro x
    by_cases hx : x = selected i
    · subst x
      simp only [LinearMap.comp_apply, blockMaps]
      rw [TensorObj.TypeGrading.blockProj_apply_mem G i
        (grade i (selected i)) (b i (selected i))
        (hhomogeneous i (selected i))]
      simp only [Submodule.coe_subtype]
    · rw [hsupported i x hx]
      by_cases hg : grade i x = grade i (selected i)
      · simp only [LinearMap.comp_apply, blockMaps]
        rw [TensorObj.TypeGrading.blockProj_apply_mem G i
          (grade i (selected i)) (b i x)
          (by simpa only [hg] using hhomogeneous i x)]
        exact (hsupported i x hx).symm
      · simp only [LinearMap.comp_apply, blockMaps]
        rw [TensorObj.TypeGrading.blockProj_apply_mem_ne G i
          (grade i (selected i)) (grade i x) (Ne.symm hg)
          (b i x) (hhomogeneous i x)]
        exact (LinearMap.map_zero _).symm
  rw [show maps = fun i ↦
      (blockMaps i).comp (G.blockProj i (grade i (selected i))) by
    funext i
    exact hfactor i]
  rw [PiTensorProduct.map_comp]
  change PiTensorProduct.map blockMaps
      (G.blockTensor (fun i ↦ grade i (selected i))) = 0
  rw [hzero]
  exact LinearMap.map_zero _
