-- Prove2me | solution 1 for mme_dwz_grouped_seven_eighths_restrict_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:30:58.578515+00:00
-- url     : https://prove2.me/submissions/2daf4005-bb58-4490-95fb-155109c8ecc5

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Theorems.Thm_mme_dwz_nonholeFraction_seven_eighths
import Theorems.Thm_mme_dwz_kronFin_hole_cover_restrict_standard
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private def groupedPositionFiberEquivForMulticopy (m : ℕ) (s : Fin 15) :
    Fin (MME.DWZTable2Counts.component s * m) ≃
      {p : GroupedPosition m // groupedOuter p = s} where
  toFun r := ⟨⟨s, r⟩, rfl⟩
  invFun p := by
    rcases p with ⟨⟨s', r⟩, hs⟩
    dsimp only [groupedOuter] at hs
    subst s'
    exact r
  left_inv r := rfl
  right_inv p := by
    rcases p with ⟨⟨s', r⟩, hs⟩
    dsimp only [groupedOuter] at hs
    subst s'
    rfl

theorem solution
    (K : Type u) [Field K] (m N ell k : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin k → Fin (8 * (N * ell + 1)) →
      BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hseven : ∀ a b,
      7 * Fintype.card (DWZStandardBlock m) ≤
        8 * (copies a b).nonholes.card) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin k → Fin (8 * (N * ell + 1)) → D.X.TypeGrading 2 :=
      fun a b ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies a b).nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ D.X))
      (TensorObj.bigAdd
        (fun r : Fin (k * (8 * (N * ell + 1))) ↦
          (G (finProdFinEquiv.symm r).1
              (finProdFinEquiv.symm r).2).blockSubtensor (fun _ ↦ 0))) := by
  classical
  dsimp only
  let D : DWZStandardLabelledData K m :=
    { X := TensorObj.kronFin 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m)
      basis := TensorObj.kronFinModePiBasis 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
        (fun r ↦ restrictedComponentZBasis K r m)
      label := groupedUsefulBlock m }
  let G : Fin k → Fin (8 * (N * ell + 1)) → D.X.TypeGrading 2 :=
    fun a b ↦ D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ (copies a b).nonholes)
  have hProfile : ∀ r : Fin 15,
      Fintype.card {p : GroupedPosition m // groupedOuter p = r} =
        MME.DWZTable2Counts.component r * m := by
    intro r
    simpa using Fintype.card_congr
      (groupedPositionFiberEquivForMulticopy m r).symm
  let : Nonempty (DWZStandardBlock m) :=
    mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
      m (groupedOuter (m := m)) hProfile
  apply mme_bigAdd_fin_mul_grouped_restrict
    (X := fun a b ↦ (G a b).blockSubtensor (fun _ ↦ 0))
    (Y := fun _ : Fin k ↦ D.X)
  intro a
  have hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ b : Fin (8 * (N * ell + 1)), nonholeFraction (copies a b) := by
    calc
      ((N * ell + 1 : ℕ) : ℝ) ≤
          7 * ((N * ell + 1 : ℕ) : ℝ) := by
        have hq : (0 : ℝ) ≤ ((N * ell + 1 : ℕ) : ℝ) := by positivity
        nlinarith
      _ = ((8 * (N * ell + 1) : ℕ) : ℝ) * ((7 : ℝ) / 8) := by
        push_cast
        ring
      _ = ∑ _b : Fin (8 * (N * ell + 1)), ((7 : ℝ) / 8) := by
        simp
      _ ≤ ∑ b : Fin (8 * (N * ell + 1)),
          nonholeFraction (copies a b) := by
        exact Finset.sum_le_sum fun b _ ↦
          mme_dwz_nonholeFraction_seven_eighths
            (copies a b) (hseven a b)
  exact mme_dwz_kronFin_hole_cover_restrict_standard
    K m N ell hN hell (copies a) hcard hsum
