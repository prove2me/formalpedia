-- Prove2me | solution 1 for mme_kronPow_position_permutation_recursive_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:10:54.09192+00:00
-- url     : https://prove2.me/submissions/aa1883ba-932d-40e3-8492-d4b79d9f6ce9

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.TensorObj MME.DWZComponentRestriction TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[simp]
private theorem kronPowModeWordBasis_succ_apply_bridge
    {K : Type u} [Field K]
    (T : TensorObj K 3) (i : Fin 3) {ι : Type u}
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

private theorem kronPowModeWordBasis_get_eq_kronPowModeBasis
    {K : Type u} [Field K]
    (T : TensorObj K 3) (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) :
    ∀ (n : ℕ) (w : PowIndex ι n),
      kronPowModeWordBasis T i b n (PowIndex.get n w) =
        kronPowModeBasis T i b n w
  | 0, w => by
      cases w
      change Basis.singleton (Fin 0 → ι) K _ =
        Basis.singleton PUnit K PUnit.unit
      simp
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      rw [kronPowModeWordBasis_succ_apply_bridge]
      rw [kronPowModeBasis]
      calc
        _ = b a ⊗ₜ[K]
              kronPowModeWordBasis T i b n (PowIndex.get n tail) := by
            rfl
        _ = b a ⊗ₜ[K] kronPowModeBasis T i b n tail := by
            rw [kronPowModeWordBasis_get_eq_kronPowModeBasis T i b n tail]
        _ = _ :=
          (Module.Basis.tensorProduct_apply' b
            (kronPowModeBasis T i b n) (a, tail)).symm

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ)
    (e : Equiv.Perm (Fin n)) (w : PowIndex ι n) :
    kronPowModePositionEquiv T i b n e
        (kronPowModeBasis T i b n w) =
      kronPowModeBasis T i b n (PowIndex.reindex e w) := by
  calc
    _ = kronPowModePositionEquiv T i b n e
          (kronPowModeWordBasis T i b n (PowIndex.get n w)) := by
        rw [kronPowModeWordBasis_get_eq_kronPowModeBasis]
    _ = kronPowModeWordBasis T i b n
          (fun r ↦ PowIndex.get n w (e r)) := by
        exact Basis.equiv_apply _ _ _ _
    _ = kronPowModeWordBasis T i b n
          (PowIndex.get n (PowIndex.reindex e w)) := by
        rw [PowIndex.get_reindex]
    _ = _ :=
      kronPowModeWordBasis_get_eq_kronPowModeBasis T i b n
        (PowIndex.reindex e w)
