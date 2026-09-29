-- Prove2me | solution 1 for mme_CW_q6_fixed_z_nondependent_pair_unit_minor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:13:15.07968+00:00
-- url     : https://prove2.me/submissions/5a7cfc6b-6ab9-4a3f-a441-f99371f9f363

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open BigOperators MME

set_option autoImplicit false

private theorem paired_sign_vectors_unit_minor
    {R ι : Type} [CommRing R]
    (c d : ι → R)
    (hpair : ∀ i,
      (c i = 0 ∧ d i = 0) ∨
        ((c i = 1 ∨ c i = -1) ∧ (d i = 1 ∨ d i = -1)))
    (hne : c ≠ d)
    (hnneg : c ≠ fun i => -d i)
    (h2 : IsUnit (2 : R)) :
    ∃ j k, IsUnit (c j * d k - c k * d j) := by
  have hdiff : ∃ j, c j ≠ d j := by
    by_contra h
    apply hne
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hsame : ∃ k, c k ≠ -d k := by
    by_contra h
    apply hnneg
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨j, hj⟩ := hdiff
  obtain ⟨k, hk⟩ := hsame
  have hjdata : IsUnit (c j) ∧ d j = -c j := by
    rcases hpair j with ⟨hc0, hd0⟩ | ⟨hc, hd⟩
    · exact False.elim (hj (hc0.trans hd0.symm))
    · rcases hc with hc1 | hcm1 <;> rcases hd with hd1 | hdm1
      · exact False.elim (hj (hc1.trans hd1.symm))
      · refine ⟨hc1 ▸ isUnit_one, ?_⟩
        simp [hc1, hdm1]
      · refine ⟨hcm1 ▸ isUnit_one.neg, ?_⟩
        simp [hcm1, hd1]
      · exact False.elim (hj (hcm1.trans hdm1.symm))
  have hkdata : IsUnit (c k) ∧ d k = c k := by
    rcases hpair k with ⟨hc0, hd0⟩ | ⟨hc, hd⟩
    · exfalso
      apply hk
      simp [hc0, hd0]
    · rcases hc with hc1 | hcm1 <;> rcases hd with hd1 | hdm1
      · exact ⟨hc1 ▸ isUnit_one, hd1.trans hc1.symm⟩
      · exfalso
        apply hk
        simp [hc1, hdm1]
      · exfalso
        apply hk
        simp [hcm1, hd1]
      · exact ⟨hcm1 ▸ isUnit_one.neg, hdm1.trans hcm1.symm⟩
  refine ⟨j, k, ?_⟩
  have hminor : c j * d k - c k * d j = 2 * c j * c k := by
    rw [hjdata.2, hkdata.2]
    ring
  rw [hminor]
  simpa only [mul_assoc] using h2.mul (hjdata.1.mul hkdata.1)

/-- Two nondependent q=6 address codes over one fixed Z-word have a unit
minor, hence define jointly uniform linear hashes. -/
theorem solution
    {M N L G : ℕ} [NeZero M]
    (e f : CWQ6ExactCoupledAddress N L G)
    (hz : e.1 2 = f.1 2)
    (hne :
      (fun j =>
        (2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) ≠
      (fun j =>
        (2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M)))
    (hnneg :
      (fun j =>
        (2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) ≠
      (fun j => -(
        (2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))))
    (h2 : IsUnit (2 : ZMod M)) :
    ∃ j k : Fin (2 * N), IsUnit (
      ((2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) *
        ((2 * ((f.1 0 k).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 k) : ZMod M)) -
      ((2 * ((e.1 0 k).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 k) : ZMod M)) *
        ((2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))) := by
  let coeff (a : CWQ6ExactCoupledAddress N L G) :
      Fin (2 * N) → ZMod M := fun j =>
    (2 * ((a.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (a.1 2 j) : ZMod M)
  let c : Fin (2 * N) → ZMod M := coeff e
  let d : Fin (2 * N) → ZMod M := coeff f
  have hcoeffZero (a : CWQ6ExactCoupledAddress N L G)
      (j : Fin (2 * N))
      (hz0 : a.1 2 j = 0) : coeff a j = 0 := by
    rcases a.2.1 j with h0 | h1 | h2 | h3
    · rcases h0 with ⟨hx, _hy, hz'⟩
      simp [coeff, hx, hz', cwQ6CoupledZHashCode]
    · rcases h1 with ⟨_hx, _hy, hz'⟩
      omega
    · rcases h2 with ⟨_hx, _hy, hz'⟩
      omega
    · rcases h3 with ⟨_hx, _hy, hz'⟩
      omega
  have hcoeffOne (a : CWQ6ExactCoupledAddress N L G)
      (j : Fin (2 * N))
      (hz1 : a.1 2 j = 1) : coeff a j = 0 := by
    rcases a.2.1 j with h0 | h1 | h2 | h3
    · rcases h0 with ⟨_hx, _hy, hz'⟩
      omega
    · rcases h1 with ⟨hx, _hy, hz'⟩
      simp [coeff, hx, hz', cwQ6CoupledZHashCode]
    · rcases h2 with ⟨_hx, _hy, hz'⟩
      omega
    · rcases h3 with ⟨_hx, _hy, hz'⟩
      omega
  have hcoeffTwo (a : CWQ6ExactCoupledAddress N L G)
      (j : Fin (2 * N))
      (hz2 : a.1 2 j = 2) : coeff a j = 1 ∨ coeff a j = -1 := by
    rcases a.2.1 j with h0 | h1 | h2 | h3
    · rcases h0 with ⟨_hx, _hy, hz'⟩
      omega
    · rcases h1 with ⟨_hx, _hy, hz'⟩
      omega
    · rcases h2 with ⟨hx, _hy, hz'⟩
      right
      simp [coeff, hx, hz', cwQ6CoupledZHashCode]
    · rcases h3 with ⟨hx, _hy, hz'⟩
      left
      simp [coeff, hx, hz', cwQ6CoupledZHashCode]
      ring
  have hpair : ∀ j,
      (c j = 0 ∧ d j = 0) ∨
        ((c j = 1 ∨ c j = -1) ∧ (d j = 1 ∨ d j = -1)) := by
    intro j
    have hzj : e.1 2 j = f.1 2 j := congrFun hz j
    generalize hez : e.1 2 j = z
    fin_cases z
    · left
      exact ⟨hcoeffZero e j hez, hcoeffZero f j (hzj.symm.trans hez)⟩
    · left
      exact ⟨hcoeffOne e j hez, hcoeffOne f j (hzj.symm.trans hez)⟩
    · right
      exact ⟨hcoeffTwo e j hez, hcoeffTwo f j (hzj.symm.trans hez)⟩
  have hne' : c ≠ d := by exact hne
  have hnneg' : c ≠ fun i => -d i := by exact hnneg
  simpa only [c, d, coeff] using
    paired_sign_vectors_unit_minor c d hpair hne' hnneg' h2
