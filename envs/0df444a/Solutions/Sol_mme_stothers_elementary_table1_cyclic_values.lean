-- Prove2me | solution 1 for mme_stothers_elementary_table1_cyclic_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:45:35.477522+00:00
-- url     : https://prove2.me/submissions/f0c11666-7b9c-4b11-b93b-445edbc34272

import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_stothers_elementary_fourth_constituent_MM_restrict

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.NumericM5.Elementary

private theorem permAut_MMq_sq
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorQ.permAut (cyclicPerm.trans cyclicPerm) (MMq K n m p) =
      MMq K m p n := by
  show TensorQ.toQ
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)) =
    TensorQ.toQ (MMObj K m p n)
  exact Quotient.sound (mme_MMObj_permObj_cyclic_sq n m p)

private theorem cyclicSymmetrization_MMObj_isomorphic
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (MMObj K n m p))
      (MMObj K (n * m * p) (n * m * p) (n * m * p)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [cyclicSymmetrization_eq_public_perm]
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  rw [← TensorQ.permAut_toQ, ← TensorQ.permAut_toQ]
  rw [permAut_MMq]
  change MMq K n m p *
      (MMq K p n m *
        TensorQ.permAut (cyclicPerm.trans cyclicPerm) (MMq K n m p)) = _
  rw [permAut_MMq_sq]
  rw [MMq_mul, MMq_mul]
  congr 1 <;> ring

private theorem HasTauValueAtLeast.of_strict_lower
    {K : Type u} [Field K] {T : TensorObj K 3}
    (tau B V : ℝ)
    (hB : 0 < B) (hV : 0 ≤ V) (hVB : V < B)
    (h : HasTauValueAtLeast T tau B) :
    HasTauValueAtLeast T tau V := by
  obtain ⟨e, he, hmultiple⟩ :=
    mme_HasTauValueAtLeast_multiple_extractions_below
      T tau B V hB hV hVB h
  have heOne : 1 ≤ e := he
  have hscale : Tendsto (fun r : ℕ ↦ r * e) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with r hr
    calc
      N ≤ r := hr
      _ = r * 1 := by simp
      _ ≤ r * e := Nat.mul_le_mul_left r heOne
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    T tau V hV (fun r : ℕ ↦ r * e) hscale (fun _ : ℕ ↦ (0 : ℝ))
      tendsto_const_nhds
  filter_upwards with r
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hmultiple r
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simpa using hweight

private theorem elementary_value_of_restrict
    {K : Type u} [Field K] {T : TensorObj K 3}
    (R : ℕ) (hR : 0 < R) (tau V : ℝ)
    (hV : 0 ≤ V) (hVB : V < (R : ℝ) ^ (3 * tau))
    (hrestrict : TensorObj.Restrict (MMObj K 1 1 R) T) :
    HasTauValueAtLeast (cyclicSymmetrization T) tau V := by
  have hcyclic : TensorObj.Restrict
      (cyclicSymmetrization (MMObj K 1 1 R))
      (cyclicSymmetrization T) :=
    mme_cyclicSymmetrization_mono_restrict hrestrict
  have hmm : TensorObj.Restrict
      (MMObj K R R R)
      (cyclicSymmetrization (MMObj K 1 1 R)) := by
    simpa only [one_mul] using
      (cyclicSymmetrization_MMObj_isomorphic
        (K := K) 1 1 R).2
  have hfull : HasTauValueAtLeast
      (cyclicSymmetrization T) tau
      ((((R * R * R : ℕ) : ℝ) ^ tau)) :=
    mme_HasTauValueAtLeast_mono_restrict (hmm.trans hcyclic)
      (mme_MMObj_tau_value (K := K) R R R tau)
  have hvalueEq :
      ((((R * R * R : ℕ) : ℝ) ^ tau)) =
        (R : ℝ) ^ (3 * tau) := by
    rw [show (((R * R * R : ℕ) : ℝ)) = (R : ℝ) ^ (3 : ℕ) by
      push_cast
      ring]
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg R) 3 tau]
    norm_num
  rw [hvalueEq] at hfull
  have hbasePos : 0 < (R : ℝ) ^ (3 * tau) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hR) _
  exact HasTauValueAtLeast.of_strict_lower tau
    ((R : ℝ) ^ (3 * tau)) V hbasePos hV hVB hfull

end MME.StothersFourth.NumericM5.Elementary

theorem solution
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ (i : Fin 5) (V : ℝ),
      0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau
        ⟨i.val, by omega⟩ →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep ⟨i.val, by omega⟩ 0)
            (MME.StothersFourth.classRep ⟨i.val, by omega⟩ 1)
            (MME.StothersFourth.classRep ⟨i.val, by omega⟩ 2)))
        tau V := by
  have htauRange : 2 ≤ 3 * tau ∧ 3 * tau ≤ 3 :=
    ⟨htauLower, htauUpper⟩
  clear htauRange htauLower htauUpper
  rcases mme_stothers_elementary_fourth_constituent_MM_restrict (K := K) 6 with
    ⟨h008, h017, h026, h035, h044⟩
  norm_num at h017 h026 h035 h044
  intro i V hV hlt
  fin_cases i
  · apply MME.StothersFourth.NumericM5.Elementary.elementary_value_of_restrict
      1 (by norm_num) tau V hV
    · simpa [MME.StothersFourth.classValue] using hlt
    · simpa [MME.StothersFourth.classRep,
        MME.StothersFourth.cwFourthBlockType] using h008
  · apply MME.StothersFourth.NumericM5.Elementary.elementary_value_of_restrict
      24 (by norm_num) tau V hV
    · norm_num [MME.StothersFourth.classValue] at hlt ⊢
      exact hlt
    · simpa [MME.StothersFourth.classRep,
        MME.StothersFourth.cwFourthBlockType] using h017
  · apply MME.StothersFourth.NumericM5.Elementary.elementary_value_of_restrict
      220 (by norm_num) tau V hV
    · norm_num [MME.StothersFourth.classValue] at hlt ⊢
      exact hlt
    · simpa [MME.StothersFourth.classRep,
        MME.StothersFourth.cwFourthBlockType] using h026
  · apply MME.StothersFourth.NumericM5.Elementary.elementary_value_of_restrict
      936 (by norm_num) tau V hV
    · norm_num [MME.StothersFourth.classValue] at hlt ⊢
      exact hlt
    · simpa [MME.StothersFourth.classRep,
        MME.StothersFourth.cwFourthBlockType] using h035
  · apply MME.StothersFourth.NumericM5.Elementary.elementary_value_of_restrict
      1734 (by norm_num) tau V hV
    · norm_num [MME.StothersFourth.classValue] at hlt ⊢
      exact hlt
    · simpa [MME.StothersFourth.classRep,
        MME.StothersFourth.cwFourthBlockType] using h044
