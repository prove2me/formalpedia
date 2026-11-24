-- Prove2me | solution 1 for stepanov_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:49:46.681839+00:00
-- url     : https://prove2.me/submissions/d32d3339-0a55-4356-999e-f56bc072e35c

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_coefficient_transformation_shift
import Theorems.Thm_stepanov_nonzero_eval_zero

section




lemma stepanov_nonzero_shift_preserves (F : Type*) [Field F] (f : Polynomial F)
    (a : AlgebraicClosure F)
    (hnsq : ¬∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f) :
    ¬∃ g : Polynomial (AlgebraicClosure F),
      g * g =
        (Polynomial.map (algebraMap F (AlgebraicClosure F)) f).comp
          (Polynomial.X + Polynomial.C a) :=
by
  rintro ⟨g, hg_sq⟩
  refine hnsq ⟨g.comp (Polynomial.X - Polynomial.C a), ?_⟩
  have h := congrArg (fun p => p.comp (Polynomial.X - Polynomial.C a)) hg_sq
  simpa [Polynomial.mul_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X] using h



lemma triangular_inversion_shift (F : Type*) [Field F]
    (a : F) (J : ℕ) (A : ℕ → Polynomial F)
    (hR : ∀ k < J,
      ∑ j ∈ Finset.Ico k J,
        (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j = 0) :
    ∀ j < J, A j = 0 :=
by
  revert A hR
  induction J with
  | zero =>
      intro A hR j hj
      exact (Nat.not_lt_zero _ hj).elim
  | succ J IH =>
      intro A hR j hj
      have hA_J : A J = 0 := by
        simpa [Nat.Ico_succ_singleton] using hR J (Nat.lt_succ_self J)
      have hR' :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
              (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j = 0 := by
        intro k hk
        have hIco : Finset.Ico k J.succ = insert J (Finset.Ico k J) := by
          simpa using
            (Finset.insert_Ico_right_eq_Ico_succ (a := k) (b := J)
              (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hk))).symm
        simpa [hIco, Finset.sum_insert, Finset.mem_Ico, hA_J] using
          hR k (Nat.lt_succ_of_lt hk)
      by_cases h_eq : j = J
      · simpa [h_eq] using hA_J
      · exact IH A hR' j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) h_eq)











lemma coefficient_transformation_degree_bound
    (F : Type*) [Field F]
    (a : F) (J d : ℕ) (A : ℕ → Polynomial F)
    (hdeg : ∀ j < J, (A j).natDegree ≤ d) :
    ∀ k < J,
      (∑ j ∈ Finset.Ico k J,
         (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j).natDegree ≤ d :=
by
  intro k _
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.Ico k J)
    (f := fun j =>
      (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j)
    (n := d) ?_
  intro j hj
  refine
    ((Polynomial.natDegree_mul_le
          (p := (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k))
          (q := A j)).trans ?_).trans
      (hdeg j (Finset.mem_Ico.1 hj).2)
  have hconst :
      ((Nat.choose j k : F) • (Polynomial.C a) ^ (j - k)).natDegree ≤ 0 :=
    (Polynomial.natDegree_smul_le
        (a := (Nat.choose j k : F))
        (p := (Polynomial.C a) ^ (j - k))).trans
      ((Polynomial.natDegree_pow_le (p := Polynomial.C a) (n := j - k)).trans
        (by simp))
  simpa [Nat.zero_add]
    using Nat.add_le_add_right hconst (A j).natDegree



end



theorem solution (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2)
    (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m)
    (hq6m : q > 6 * m)
    (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J, (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
                     (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
  (f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * (Polynomial.X) ^ (j * q)))) = 0 ↔
    (∀ j < J, rj j = 0 ∧ sj j = 0) :=
by
  constructor
  · intro hsum
    by_cases hf0 : f.eval 0 ≠ 0
    · exact
        (stepanov_nonzero_eval_zero (F := F) (hF := hF)
          (f := f) (q := q) (m := m) (ℓ := ℓ) (J := J) (c := c)
          (hc := hc) (hq := hq) (hfdeg := hfdeg) (hm_pos := hm_pos)
          (hq6m := hq6m) (hf0 := hf0)
          (rj := rj) (sj := sj) (hnsq := hnsq) (hdeg := hdeg)).mp hsum
    · have hqm : q > m :=
        lt_of_le_of_lt
          (by
            have h := Nat.mul_le_mul_right m (by decide : (1 : ℕ) ≤ 6)
            simpa using h)
          hq6m
      obtain ⟨a, hfa_ne⟩ :=
        Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f
          (by
            intro hf
            simp [hf] at hfdeg
            omega)
          (by
            rw [Cardinal.mk_fintype, hfdeg, ← hq]
            exact_mod_cast hqm)
      let shift : Polynomial F := Polynomial.X + Polynomial.C a
      let g : Polynomial F := f.comp shift
      let rj' : ℕ → Polynomial F := fun j => (rj j).comp shift
      let sj' : ℕ → Polynomial F := fun j => (sj j).comp shift
      have hg0_ne : g.eval 0 ≠ 0 := by
        simpa [g, shift] using hfa_ne
      have hgdeg : g.natDegree = m := by
        simp [g, shift, hfdeg, Polynomial.natDegree_comp]
      have hmap_g :
          Polynomial.map (algebraMap F (AlgebraicClosure F)) g =
            (Polynomial.map (algebraMap F (AlgebraicClosure F)) f).comp
              (Polynomial.X +
                Polynomial.C (algebraMap F (AlgebraicClosure F) a)) := by
        unfold g shift
        have h :=
          Polynomial.map_comp (algebraMap F (AlgebraicClosure F)) f
            (Polynomial.X + Polynomial.C a)
        have hshift :
            Polynomial.map (algebraMap F (AlgebraicClosure F))
                (Polynomial.X + Polynomial.C a : Polynomial F) =
              (Polynomial.X +
                Polynomial.C (algebraMap F (AlgebraicClosure F) a)
                  : Polynomial (AlgebraicClosure F)) := by
          simp [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
        simpa [hshift] using h
      have hnsq_g :
          ¬ ∃ h : Polynomial (AlgebraicClosure F),
              h * h =
                Polynomial.map (algebraMap F (AlgebraicClosure F)) g := by
        have hnsq_shifted :=
          stepanov_nonzero_shift_preserves (F := F) (f := f)
            (a := algebraMap F (AlgebraicClosure F) a) hnsq
        simpa [hmap_g] using hnsq_shifted
      have hdeg_shifted :
          ∀ j < J,
            (rj' j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
            (sj' j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 := by
        intro j hj
        simpa [rj', sj', shift, Polynomial.natDegree_comp] using hdeg j hj
      have hg1 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) * shift ^ (j * q)) = 0 := by
        simpa [shift, g, rj', sj'] using
          congrArg (fun p : Polynomial F => p.comp shift) hsum
      have hshift_pow :
          ∀ j : ℕ,
            shift ^ (j * q) =
              (Polynomial.X ^ q + Polynomial.C a : Polynomial F) ^ j := by
        intro j
        have h1 : shift ^ (j * q) = (shift ^ q) ^ j := by
          simpa [Nat.mul_comm] using (pow_mul shift q j)
        have h2 :
            shift ^ q = (Polynomial.X ^ q + Polynomial.C a : Polynomial F) := by
          have h :=
            (FiniteField.expand_card
                (Polynomial.X + Polynomial.C a : Polynomial F)).symm
          simpa [shift, hq, map_add, Polynomial.expand_X, Polynomial.expand_C] using h
        simp [h1, h2]
      have hg2 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) *
                    (Polynomial.X ^ q + Polynomial.C a : Polynomial F) ^ j) =
            0 := by
        have hsum_eq :
            Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) * shift ^ (j * q)) =
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj' j) + (sj' j) * g ^ c) *
                    (Polynomial.X ^ q + Polynomial.C a : Polynomial F) ^ j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [hshift_pow j]
        simpa [hsum_eq] using hg1
      let t : Polynomial F := Polynomial.X ^ q + Polynomial.C a
      let sum_total : Polynomial F :=
        ∑ j ∈ Finset.range J,
          ((rj' j) + (sj' j) * g ^ c) * t ^ j
      have hg2' : g ^ ℓ * sum_total = 0 := by
        simpa [t, sum_total] using hg2
      let sum_r : Polynomial F :=
        ∑ j ∈ Finset.range J, rj' j * t ^ j
      let sum_s_base : Polynomial F :=
        ∑ j ∈ Finset.range J, sj' j * t ^ j
      have hsum_split :
          sum_total = sum_r + g ^ c * sum_s_base := by
        unfold sum_total sum_r sum_s_base
        calc
          (∑ j ∈ Finset.range J,
              ((rj' j) + (sj' j) * g ^ c) * t ^ j)
              = ∑ j ∈ Finset.range J,
                  (rj' j * t ^ j + (sj' j * g ^ c) * t ^ j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    simp [add_mul]
          _ = (∑ j ∈ Finset.range J, rj' j * t ^ j) +
                ∑ j ∈ Finset.range J, (sj' j * g ^ c) * t ^ j := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (Finset.sum_add_distrib
                    (s := Finset.range J)
                    (f := fun j => rj' j * t ^ j)
                    (g := fun j => (sj' j * g ^ c) * t ^ j))
          _ = (∑ j ∈ Finset.range J, rj' j * t ^ j) +
                g ^ c * ∑ j ∈ Finset.range J, sj' j * t ^ j := by
                have h :
                  ∑ j ∈ Finset.range J, (sj' j * g ^ c) * t ^ j =
                    g ^ c * ∑ j ∈ Finset.range J, sj' j * t ^ j := by
                  have h1 :
                    (∑ j ∈ Finset.range J, (sj' j * g ^ c) * t ^ j) =
                      ∑ j ∈ Finset.range J, g ^ c * (sj' j * t ^ j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ac_rfl
                  have h2 :
                    g ^ c * ∑ j ∈ Finset.range J, sj' j * t ^ j =
                      ∑ j ∈ Finset.range J, g ^ c * (sj' j * t ^ j) := by
                    exact
                      Finset.mul_sum
                        (s := Finset.range J)
                        (f := fun j => sj' j * t ^ j)
                        (a := g ^ c)
                  exact h1.trans h2.symm
                simp [h]
      let R : ℕ → Polynomial F := fun k =>
        ∑ j ∈ Finset.Ico k J,
          (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * rj' j
      let S : ℕ → Polynomial F := fun k =>
        ∑ j ∈ Finset.Ico k J,
          (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * sj' j
      have hcoeff_r :
          sum_r =
            ∑ k ∈ Finset.range J,
              R k * Polynomial.X ^ (k * q) := by
        unfold sum_r R t
        simpa using
          (coefficient_transformation_shift (F := F)
            (a := a) (q := q) (J := J) (A := rj'))
      have hcoeff_s_base :
          sum_s_base =
            ∑ k ∈ Finset.range J,
              S k * Polynomial.X ^ (k * q) := by
        unfold sum_s_base t S
        simpa using
          (coefficient_transformation_shift (F := F)
            (a := a) (q := q) (J := J) (A := sj'))
      have hsum_total_eq :
          sum_total =
            ∑ k ∈ Finset.range J,
              (R k + S k * g ^ c) * Polynomial.X ^ (k * q) := by
        calc
          sum_total = sum_r + g ^ c * sum_s_base := hsum_split
          _ =
              (∑ k ∈ Finset.range J,
                  R k * Polynomial.X ^ (k * q)) +
                g ^ c * sum_s_base := by
                rw [hcoeff_r]
          _ =
              (∑ k ∈ Finset.range J,
                  R k * Polynomial.X ^ (k * q)) +
                g ^ c *
                  (∑ k ∈ Finset.range J,
                    S k * Polynomial.X ^ (k * q)) := by
                rw [hcoeff_s_base]
          _ =
              (∑ k ∈ Finset.range J,
                  R k * Polynomial.X ^ (k * q)) +
                ∑ k ∈ Finset.range J,
                  g ^ c * (S k * Polynomial.X ^ (k * q)) := by
                have hmul :
                    g ^ c *
                        ∑ k ∈ Finset.range J,
                          S k * Polynomial.X ^ (k * q) =
                      ∑ k ∈ Finset.range J,
                        g ^ c * (S k * Polynomial.X ^ (k * q)) := by
                  exact
                    Finset.mul_sum
                      (s := Finset.range J)
                      (f := fun k => S k * Polynomial.X ^ (k * q))
                      (a := g ^ c)
                have :=
                  congrArg
                    (fun p =>
                      (∑ k ∈ Finset.range J,
                          R k * Polynomial.X ^ (k * q)) + p)
                    hmul
                simpa using this
          _ =
              ∑ k ∈ Finset.range J,
                (R k * Polynomial.X ^ (k * q) +
                  g ^ c * (S k * Polynomial.X ^ (k * q))) := by
                have :=
                  Finset.sum_add_distrib
                    (s := Finset.range J)
                    (f := fun k => R k * Polynomial.X ^ (k * q))
                    (g := fun k =>
                      g ^ c * (S k * Polynomial.X ^ (k * q)))
                simpa [add_comm, add_left_comm, add_assoc] using this.symm
          _ =
              ∑ k ∈ Finset.range J,
                (R k + S k * g ^ c) * Polynomial.X ^ (k * q) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                calc
                  R k * Polynomial.X ^ (k * q) +
                      g ^ c * (S k * Polynomial.X ^ (k * q)) =
                      R k * Polynomial.X ^ (k * q) +
                        (S k * g ^ c) * Polynomial.X ^ (k * q) := by
                          ac_rfl
                  _ =
                      (R k + S k * g ^ c) *
                        Polynomial.X ^ (k * q) := by
                        rw [add_mul]
      have hg3 :
          g ^ ℓ *
              Finset.sum (Finset.range J)
                (fun k =>
                  (R k + S k * g ^ c) * Polynomial.X ^ (k * q)) = 0 := by
        simpa [sum_total, hsum_total_eq] using hg2'
      have hdeg_RS :
          ∀ k < J,
            (R k).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
            (S k).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 := by
        intro k hk
        refine ⟨?_, ?_⟩
        · simpa [R] using
            coefficient_transformation_degree_bound
              (F := F) (a := a) (J := J)
              (d := Nat.ceil (((q : ℚ) - m) / 2) - 1)
              (A := rj')
              (hdeg := fun j hj => (hdeg_shifted j hj).1)
              k hk
        · simpa [S] using
            coefficient_transformation_degree_bound
              (F := F) (a := a) (J := J)
              (d := Nat.ceil (((q : ℚ) - m) / 2) - 1)
              (A := sj')
              (hdeg := fun j hj => (hdeg_shifted j hj).2)
              k hk
      have hstep_g : ∀ k < J, R k = 0 ∧ S k = 0 :=
        (stepanov_nonzero_eval_zero (F := F) (hF := hF)
          (f := g) (q := q) (m := m) (ℓ := ℓ) (J := J) (c := c)
          (hc := hc) (hq := hq) (hfdeg := hgdeg) (hm_pos := hm_pos)
          (hq6m := hq6m) (hf0 := hg0_ne)
          (rj := R) (sj := S) (hnsq := hnsq_g) (hdeg := hdeg_RS)).mp hg3
      have hR_eq_zero :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
                (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * rj' j = 0 :=
        fun k hk => by
          simpa [R] using (hstep_g k hk).1
      have hS_eq_zero :
          ∀ k < J,
            ∑ j ∈ Finset.Ico k J,
                (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * sj' j = 0 :=
        fun k hk => by
          simpa [S] using (hstep_g k hk).2
      have hrj'_zero : ∀ j < J, rj' j = 0 :=
        triangular_inversion_shift (F := F) (a := a) (J := J)
          (A := rj') hR_eq_zero
      have hsj'_zero : ∀ j < J, sj' j = 0 :=
        triangular_inversion_shift (F := F) (a := a) (J := J)
          (A := sj') hS_eq_zero
      intro j hj
      have hrj_comp_zero : (rj j).comp (Polynomial.X + Polynomial.C a) = 0 := by
        simpa [rj', shift] using hrj'_zero j hj
      have hsj_comp_zero : (sj j).comp (Polynomial.X + Polynomial.C a) = 0 := by
        simpa [sj', shift] using hsj'_zero j hj
      exact
        ⟨(Polynomial.comp_X_add_C_eq_zero_iff (p := rj j) (t := a)).mp
            hrj_comp_zero,
          (Polynomial.comp_X_add_C_eq_zero_iff (p := sj j) (t := a)).mp
            hsj_comp_zero⟩
  · intro hall
    have :
        Finset.sum (Finset.range J)
            (fun j =>
              ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        obtain ⟨hrj, hsj⟩ := hall j (Finset.mem_range.mp hj)
        simp [hrj, hsj]
    simp [this]
