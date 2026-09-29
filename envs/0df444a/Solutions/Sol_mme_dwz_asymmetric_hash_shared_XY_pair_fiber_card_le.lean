-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:43:07.323505+00:00
-- url     : https://prove2.me/submissions/c1dcb909-78f2-457f-ba2b-9324855a0e1e

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_ZMod_two_linear_hash_finset_fiber_card_le

open BigOperators

set_option autoImplicit false
set_option warningAsError true

open MME

private theorem pair_card_le_of_weight_collision
    {p N : ℕ} [Fact p.Prime]
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K I' J' K' U U' : Fin (N + 1) → ZMod p)
    (hUU' : U ≠ U')
    (hcollision : ∀ q,
      dwzAsymmetricAffineRetains levelSum S I J K q →
      dwzAsymmetricAffineRetains levelSum S I' J' K' q →
      (∑ t, U t * q.1 t.castSucc) =
        ∑ t, U' t * q.1 t.castSucc) :
    ((dwzAsymmetricAffineStatesRetaining levelSum S I J K) ∩
      (dwzAsymmetricAffineStatesRetaining levelSum S I' J' K')).card ≤
        S.card * p ^ N := by
  classical
  let P :=
    (dwzAsymmetricAffineStatesRetaining levelSum S I J K) ∩
      (dwzAsymmetricAffineStatesRetaining levelSum S I' J' K')
  let c : Fin (N + 2) → ZMod p :=
    Fin.lastCases 1 (fun t : Fin (N + 1) ↦ I t)
  let d : Fin (N + 2) → ZMod p :=
    Fin.lastCases 0 (fun t : Fin (N + 1) ↦ U t - U' t)
  let offset : (Fin (N + 2) → ZMod p) → ZMod p := fun W ↦
    (∑ t : Fin (N + 1), I t * W t.castSucc) -
      ∑ t : Fin (N + 1), J t * W t.castSucc
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hUU'
  have hdiff : U j - U' j ≠ 0 := by
    intro hzero
    exact hj (sub_eq_zero.mp hzero)
  have hdet : IsUnit
      (c j.castSucc * d (Fin.last (N + 1)) -
        c (Fin.last (N + 1)) * d j.castSucc) := by
    have heval :
        c j.castSucc * d (Fin.last (N + 1)) -
            c (Fin.last (N + 1)) * d j.castSucc =
          -(U j - U' j) := by
      simp [c, d]
    rw [heval]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hdiff)
  have hw0 (q : (Fin (N + 2) → ZMod p) × ZMod p)
      (hq : dwzAsymmetricAffineRetains levelSum S I J K q) :
      q.2 = offset q.1 := by
    obtain ⟨s, _hsS, hX, hY, _hZ⟩ := hq
    have hX' :
        q.1 (Fin.last (N + 1)) +
            ∑ t : Fin (N + 1), I t * q.1 t.castSucc = s := by
      simpa only [dwzAsymmetricHashX,
        dwzAsymmetricHashStateOfAffine] using hX
    have hY' :
        q.1 (Fin.last (N + 1)) + q.2 +
            ∑ t : Fin (N + 1), J t * q.1 t.castSucc = s := by
      simpa only [dwzAsymmetricHashY,
        dwzAsymmetricHashStateOfAffine] using hY
    dsimp only [offset]
    apply (eq_sub_iff_add_eq).2
    have heq := hY'.trans hX'.symm
    exact add_left_cancel (a := q.1 (Fin.last (N + 1)))
      (by simpa [add_assoc] using heq)
  let Q : Finset (Fin (N + 2) → ZMod p) :=
    Finset.univ.filter (fun W ↦
      (∑ i, c i * W i) ∈ S ∧ (∑ i, d i * W i) = 0)
  have hmaps : Set.MapsTo Prod.fst (↑P : Set
      ((Fin (N + 2) → ZMod p) × ZMod p)) (↑Q : Set _) := by
    intro q hq
    have hqP : q ∈ P := hq
    have hqmem := Finset.mem_inter.mp hqP
    have hq1 : dwzAsymmetricAffineRetains levelSum S I J K q := by
      simpa only [dwzAsymmetricAffineStatesRetaining,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqmem.1
    have hq2 : dwzAsymmetricAffineRetains levelSum S I' J' K' q := by
      simpa only [dwzAsymmetricAffineStatesRetaining,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqmem.2
    have hcoll := hcollision q hq1 hq2
    obtain ⟨s, hsS, hX, _hY, _hZ⟩ := hq1
    have hcLabel : (∑ i, c i * q.1 i) = s := by
      rw [Fin.sum_univ_castSucc]
      simpa [c, add_comm, dwzAsymmetricHashX,
        dwzAsymmetricHashStateOfAffine] using hX
    have hdZero : (∑ i, d i * q.1 i) = 0 := by
      rw [Fin.sum_univ_castSucc]
      simp only [d, Fin.lastCases_castSucc, Fin.lastCases_last,
        zero_mul, add_zero]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, hcoll, sub_self]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcLabel.symm ▸ hsS, hdZero⟩
  have hinj : Set.InjOn Prod.fst (↑P : Set
      ((Fin (N + 2) → ZMod p) × ZMod p)) := by
    intro q hq r hr hqr
    have hqmem := Finset.mem_inter.mp (show q ∈ P from hq)
    have hrmem := Finset.mem_inter.mp (show r ∈ P from hr)
    have hq1 : dwzAsymmetricAffineRetains levelSum S I J K q := by
      simpa only [dwzAsymmetricAffineStatesRetaining,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqmem.1
    have hr1 : dwzAsymmetricAffineRetains levelSum S I J K r := by
      simpa only [dwzAsymmetricAffineStatesRetaining,
        Finset.mem_filter, Finset.mem_univ, true_and] using hrmem.1
    apply Prod.ext hqr
    rw [hw0 q hq1, hw0 r hr1, hqr]
  have hQ : Q.card ≤ S.card * p ^ N := by
    exact mme_ZMod_two_linear_hash_finset_fiber_card_le
      c d j.castSucc (Fin.last (N + 1)) hdet S 0
  calc
    ((dwzAsymmetricAffineStatesRetaining levelSum S I J K) ∩
      (dwzAsymmetricAffineStatesRetaining levelSum S I' J' K')).card =
        P.card := rfl
    _ ≤ Q.card := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
    _ ≤ S.card * p ^ N := hQ

theorem solution
    {p N : ℕ} [Fact p.Prime]
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K I' J' K' : Fin (N + 1) → ZMod p)
    (hshare : (I = I' ∧ J ≠ J') ∨ (J = J' ∧ I ≠ I')) :
    ((dwzAsymmetricAffineStatesRetaining levelSum S I J K) ∩
      (dwzAsymmetricAffineStatesRetaining levelSum S I' J' K')).card ≤
        S.card * p ^ N := by
  rcases hshare with ⟨hI, hJ⟩ | ⟨hJ, hI⟩
  · apply pair_card_le_of_weight_collision
      levelSum S I J K I' J' K' J J' hJ
    intro q hq hq'
    obtain ⟨s, _hs, hX, hY, _hZ⟩ := hq
    obtain ⟨s', _hs', hX', hY', _hZ'⟩ := hq'
    have hlabel : s = s' := by
      calc
        s = dwzAsymmetricHashX
            (dwzAsymmetricHashStateOfAffine q) I := hX.symm
        _ = dwzAsymmetricHashX
            (dwzAsymmetricHashStateOfAffine q) I' := by rw [hI]
        _ = s' := hX'
    have heq := hY.trans (hlabel.trans hY'.symm)
    simp only [dwzAsymmetricHashY,
      dwzAsymmetricHashStateOfAffine] at heq
    exact add_left_cancel
      (a := q.1 (Fin.last (N + 1)) + q.2)
      (by simpa [add_assoc] using heq)
  · apply pair_card_le_of_weight_collision
      levelSum S I J K I' J' K' I I' hI
    intro q hq hq'
    obtain ⟨s, _hs, hX, hY, _hZ⟩ := hq
    obtain ⟨s', _hs', hX', hY', _hZ'⟩ := hq'
    have hlabel : s = s' := by
      calc
        s = dwzAsymmetricHashY
            (dwzAsymmetricHashStateOfAffine q) J := hY.symm
        _ = dwzAsymmetricHashY
            (dwzAsymmetricHashStateOfAffine q) J' := by rw [hJ]
        _ = s' := hY'
    have heq := hX.trans (hlabel.trans hX'.symm)
    simp only [dwzAsymmetricHashX,
      dwzAsymmetricHashStateOfAffine] at heq
    exact add_left_cancel (a := q.1 (Fin.last (N + 1)))
      (by simpa [add_assoc] using heq)
