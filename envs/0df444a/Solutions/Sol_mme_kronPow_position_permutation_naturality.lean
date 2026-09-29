-- Prove2me | solution 1 for mme_kronPow_position_permutation_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:54:27.628879+00:00
-- url     : https://prove2.me/submissions/3d577b5f-d5ed-4bfc-b975-498c73f00b42

import Definitions.Def_mme_kronPow_position_permutation_linear_data

open MME MME.TensorObj TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[simp]
private theorem kronPowModeWordBasis_succ_apply_naturality
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (w : Fin (n + 1) → ι) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K]
        kronPowModeWordBasis T i b n (fun r ↦ w r.succ) := by
  rw [kronPowModeWordBasis]
  calc
    _ = (Module.Basis.tensorProduct b
          (kronPowModeWordBasis T i b n))
        ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).symm w) :=
      Module.Basis.reindex_apply _ _ _
    _ = _ := by
      rw [Fin.consEquiv_symm_apply,
        Module.Basis.tensorProduct_apply]
      rfl

@[simp]
private theorem kronPowModePositionEquiv_basis_naturality
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (e : Equiv.Perm (Fin n))
    (w : Fin n → ι) :
    kronPowModePositionEquiv T i b n e
        (kronPowModeWordBasis T i b n w) =
      kronPowModeWordBasis T i b n (fun r ↦ w (e r)) := by
  exact Basis.equiv_apply _ _ _ _

private theorem kronPowModeMap_word_basis_naturality
    {K : Type u} [Field K] {d : ℕ}
    {T S : TensorObj K d} (i : Fin d)
    {ι κ : Type u}
    (b : Basis ι K (T.V i)) (c : Basis κ K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (σ : ι → κ)
    (hf : ∀ a, f (b a) = c (σ a))
    (n : ℕ) (w : Fin n → ι) :
    kronPowModeMap i f n (kronPowModeWordBasis T i b n w) =
      kronPowModeWordBasis S i c n (fun r ↦ σ (w r)) := by
  induction n with
  | zero =>
      change LinearMap.id (Basis.singleton (Fin 0 → ι) K w) =
        Basis.singleton (Fin 0 → κ) K (fun r ↦ σ (w r))
      simp
      try rfl
  | succ n ih =>
      rw [kronPowModeWordBasis_succ_apply_naturality,
        kronPowModeWordBasis_succ_apply_naturality]
      change
        TensorProduct.map f (kronPowModeMap i f n)
            (b (w 0) ⊗ₜ[K]
              kronPowModeWordBasis T i b n (fun r ↦ w r.succ)) = _
      rw [TensorProduct.map_tmul, hf, ih]

theorem solution
    {K : Type u} [Field K] {d : ℕ}
    {T S : TensorObj K d} (i : Fin d)
    {ι κ : Type u}
    (b : Basis ι K (T.V i)) (c : Basis κ K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (σ : ι → κ)
    (hf : ∀ a, f (b a) = c (σ a))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (kronPowModeMap i f n).comp
        (kronPowModePositionEquiv T i b n e).toLinearMap =
      (kronPowModePositionEquiv S i c n e).toLinearMap.comp
        (kronPowModeMap i f n) := by
  apply (kronPowModeWordBasis T i b n).ext
  intro w
  change
    kronPowModeMap i f n
        (kronPowModePositionEquiv T i b n e
          (kronPowModeWordBasis T i b n w)) =
      kronPowModePositionEquiv S i c n e
        (kronPowModeMap i f n
          (kronPowModeWordBasis T i b n w))
  rw [kronPowModePositionEquiv_basis_naturality]
  rw [kronPowModeMap_word_basis_naturality (σ := σ) (hf := hf)]
  rw [kronPowModeMap_word_basis_naturality (σ := σ) (hf := hf)]
  rw [kronPowModePositionEquiv_basis_naturality]
