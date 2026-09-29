-- Prove2me | solution 1 for mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:01:00.372545+00:00
-- url     : https://prove2.me/submissions/476edf9a-47f9-4971-a35a-28ab69220e1f

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Distinct exact q=6 addresses sharing an X- or Y-word give two
independent X-minus-Z difference forms over every nonzero modulus. -/
theorem solution
    {M N L G : ℕ} [NeZero M]
    (e f : CWQ6ExactCoupledAddress N L G)
    (hne : e ≠ f)
    (hshare : e.1 0 = f.1 0 ∨ e.1 1 = f.1 1) :
    ∃ j k : Fin (2 * N), IsUnit (
      ((2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) *
        ((2 * ((f.1 0 k).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 k) : ZMod M)) -
      ((2 * ((e.1 0 k).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 k) : ZMod M)) *
        ((2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))) := by
  classical
  let coeff (a : CWQ6ExactCoupledAddress N L G) :
      Fin (2 * N) → ZMod M := fun j =>
    (2 * ((a.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (a.1 2 j) : ZMod M)
  have haddr_of_xz (hx : e.1 0 = f.1 0) (hz : e.1 2 = f.1 2) : e = f := by
    apply Subtype.ext
    funext i j
    fin_cases i
    · exact congrFun hx j
    · have hxj := congrFun hx j
      have hzj := congrFun hz j
      rcases e.2.1 j with ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ |
          ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ <;>
        rcases f.2.1 j with ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ |
          ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ <;> simp_all
    · exact congrFun hz j
  have haddr_of_yz (hy : e.1 1 = f.1 1) (hz : e.1 2 = f.1 2) : e = f := by
    apply Subtype.ext
    funext i j
    fin_cases i
    · have hyj := congrFun hy j
      have hzj := congrFun hz j
      rcases e.2.1 j with ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ |
          ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ <;>
        rcases f.2.1 j with ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ |
          ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ <;> simp_all
    · exact congrFun hy j
    · exact congrFun hz j
  have hzNe : e.1 2 ≠ f.1 2 := by
    intro hz
    rcases hshare with hx | hy
    · exact hne (haddr_of_xz hx hz)
    · exact hne (haddr_of_yz hy hz)
  obtain ⟨j, hjne⟩ := Function.ne_iff.mp hzNe
  have hjorient :
      (e.1 2 j = 2 ∧ f.1 2 j ≠ 2) ∨
        (f.1 2 j = 2 ∧ e.1 2 j ≠ 2) := by
    rcases hshare with hx | hy
    · have hxj := congrFun hx j
      rcases e.2.1 j with ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ |
          ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ <;>
        rcases f.2.1 j with ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ |
          ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ <;> simp_all
    · have hyj := congrFun hy j
      rcases e.2.1 j with ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ |
          ⟨hex, hey, hez⟩ | ⟨hex, hey, hez⟩ <;>
        rcases f.2.1 j with ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ |
          ⟨hfx, hfy, hfz⟩ | ⟨hfx, hfy, hfz⟩ <;> simp_all
  let Ze : Finset (Fin (2 * N)) := Finset.univ.filter (fun i => e.1 2 i = 2)
  let Zf : Finset (Fin (2 * N)) := Finset.univ.filter (fun i => f.1 2 i = 2)
  have hZeCard : Ze.card = 2 * G := by
    simpa [Ze, cwQ6CoupledMarginalMultiplicity] using
      e.2.2 (2 : Fin 3) (2 : Fin 3)
  have hZfCard : Zf.card = 2 * G := by
    simpa [Zf, cwQ6CoupledMarginalMultiplicity] using
      f.2.2 (2 : Fin 3) (2 : Fin 3)
  have hcoeffZero (a : CWQ6ExactCoupledAddress N L G) (i : Fin (2 * N))
      (hi : a.1 2 i ≠ 2) : coeff a i = 0 := by
    rcases a.2.1 i with h0 | h1 | h2 | h3
    · simp [coeff, h0.1, h0.2.2, cwQ6CoupledZHashCode]
    · simp [coeff, h1.1, h1.2.2, cwQ6CoupledZHashCode]
    · exact False.elim (hi h2.2.2)
    · exact False.elim (hi h3.2.2)
  have hcoeffUnit (a : CWQ6ExactCoupledAddress N L G) (i : Fin (2 * N))
      (hi : a.1 2 i = 2) : IsUnit (coeff a i) := by
    rcases a.2.1 i with h0 | h1 | h2 | h3
    · omega
    · omega
    · have hc : coeff a i = -1 := by
        simp [coeff, h2.1, h2.2.2, cwQ6CoupledZHashCode]
      rw [hc]
      exact isUnit_one.neg
    · have hc : coeff a i = 1 := by
        simp [coeff, h3.1, h3.2.2, cwQ6CoupledZHashCode]
        ring
      rw [hc]
      exact isUnit_one
  rcases hjorient with hj | hj
  · have hjZe : j ∈ Ze := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩
    have hjNotZf : j ∉ Zf := by simp [Zf, hj.2]
    have hnsub : ¬ Zf ⊆ Ze := by
      intro hsub
      have heq : Zf = Ze := Finset.eq_of_subset_of_card_le hsub (by omega)
      have : j ∈ Zf := by simpa [heq] using hjZe
      exact hjNotZf this
    obtain ⟨k, hkZf, hkNotZe⟩ := Finset.not_subset.mp hnsub
    have hkf : f.1 2 k = 2 := (Finset.mem_filter.mp hkZf).2
    have hke : e.1 2 k ≠ 2 := by simpa [Ze] using hkNotZe
    refine ⟨j, k, ?_⟩
    change IsUnit (coeff e j * coeff f k - coeff e k * coeff f j)
    rw [hcoeffZero e k hke, hcoeffZero f j hj.2, zero_mul]
    simpa only [sub_zero] using
      (hcoeffUnit e j hj.1).mul (hcoeffUnit f k hkf)
  · have hjZf : j ∈ Zf := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩
    have hjNotZe : j ∉ Ze := by simp [Ze, hj.2]
    have hnsub : ¬ Ze ⊆ Zf := by
      intro hsub
      have heq : Ze = Zf := Finset.eq_of_subset_of_card_le hsub (by omega)
      have : j ∈ Ze := by simpa [heq] using hjZf
      exact hjNotZe this
    obtain ⟨k, hkZe, hkNotZf⟩ := Finset.not_subset.mp hnsub
    have hke : e.1 2 k = 2 := (Finset.mem_filter.mp hkZe).2
    have hkf : f.1 2 k ≠ 2 := by simpa [Zf] using hkNotZf
    refine ⟨k, j, ?_⟩
    change IsUnit (coeff e k * coeff f j - coeff e j * coeff f k)
    rw [hcoeffZero e j hj.2, hcoeffZero f k hkf, zero_mul]
    simpa only [sub_zero] using
      (hcoeffUnit e k hke).mul (hcoeffUnit f j hj.1)
