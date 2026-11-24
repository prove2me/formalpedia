-- Prove2me | solution 1 for stepanov_nonzero_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:35:48.339385+00:00
-- url     : https://prove2.me/submissions/05157648-128c-419e-a2f6-75164b9fd65c

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
import Theorems.Thm_stepanov_nonzero_polynomial_equality
import Theorems.Thm_stepanov_square_from_eq

section










lemma stepanov_nonzero_minimal_congruence
    (F : Type*) [Field F]
    (f : Polynomial F) (ℓ c q J : ℕ)
    (rj sj : ℕ → Polynomial F)
    (hf : f ≠ 0)
    (hsum : f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) *
          (Polynomial.X) ^ (j * q))) = 0)
    (k : ℕ) (hk : k < J)
    (hk_min : ∀ j < k, rj j = 0 ∧ sj j = 0) :
    Polynomial.X ^ q ∣ (rj k + sj k * f ^ c) :=
by
  have hsum_zero :
      ∑ j ∈ Finset.range J,
        (rj j + sj j * f ^ c) * Polynomial.X ^ (j * q) = 0 := by
    simpa using
      (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ hf)
  rw [
    Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (Nat.le_of_lt hk),
    Finset.sum_eq_zero (by
      intro j hj
      obtain ⟨hrj, hsj⟩ := hk_min j (Finset.mem_Ico.mp hj).2
      simp [hrj, hsj]),
    zero_add,
    ← Finset.insert_Ico_succ_left_eq_Ico hk,
    Finset.sum_insert (by simp [Finset.mem_Ico])
  ] at hsum_zero
  have h_dvd_term :
      Polynomial.X ^ ((k + 1) * q) ∣
        (rj k + sj k * f ^ c) * Polynomial.X ^ (k * q) := by
    rw [add_eq_zero_iff_eq_neg.mp hsum_zero]
    refine dvd_neg.mpr ?_
    refine Finset.dvd_sum ?_
    intro x hx
    exact dvd_mul_of_dvd_right
      (pow_dvd_pow Polynomial.X
        (Nat.mul_le_mul_right q (Finset.mem_Ico.mp hx).1)) _
  refine
    (mul_dvd_mul_iff_left (a := Polynomial.X ^ (k * q))
        (pow_ne_zero _ Polynomial.X_ne_zero)).mp ?_
  have hkq : (k + 1) * q = k * q + q := by ring
  simpa [pow_add, hkq, mul_comm, mul_left_comm, mul_assoc] using h_dvd_term





lemma degree_bound_implies_two_mul_add_lt (q m n : ℕ) (hqm : m < q)
    (hn : n ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) : 2 * n + m < q :=
by
  have hx_pos : (0 : ℚ) < ((q : ℚ) - m) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast hqm)) (by norm_num)
  have hn_lt : (n : ℚ) < ((q : ℚ) - m) / 2 :=
    Nat.lt_ceil.mp <| Nat.lt_of_le_pred (Nat.ceil_pos.mpr hx_pos) hn
  exact_mod_cast
    (show (2 : ℚ) * n + m < (q : ℚ) from by nlinarith [hn_lt])







end



theorem solution (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2)
    (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m)
    (hq6m : q > 6 * m)
    (hf0 : f.eval 0 ≠ 0)
    (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J,
      (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
      (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
  (f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * (Polynomial.X) ^ (j * q)))) = 0 ↔
    (∀ j < J, rj j = 0 ∧ sj j = 0) :=
by
  classical
  constructor
  · intro hsum
    by_contra h
    push_neg at h
    obtain ⟨j₀, hj₀_lt, hj₀_ne⟩ := h
    have hj₀_or : rj j₀ ≠ 0 ∨ sj j₀ ≠ 0 := by
      by_cases hrj : rj j₀ = 0
      · right; exact hj₀_ne hrj
      · left; exact hrj
    have hP_exists : ∃ k, k < J ∧ (rj k ≠ 0 ∨ sj k ≠ 0) :=
      ⟨j₀, hj₀_lt, hj₀_or⟩
    let k := Nat.find hP_exists
    obtain ⟨hk, hk_nonzero⟩ := Nat.find_spec hP_exists
    have hk_min : ∀ j < k, rj j = 0 ∧ sj j = 0 := fun j hj => by
      have h' : j < J → rj j = 0 ∧ sj j = 0 := by
        simpa [not_and, not_or, not_not] using
          (Nat.find_min hP_exists hj :
            ¬ (j < J ∧ (rj j ≠ 0 ∨ sj j ≠ 0)))
      exact h' (Nat.lt_trans hj hk)
    have heq :=
      stepanov_nonzero_polynomial_equality F hF f (rj k) (sj k) q m c hq hfdeg hc
        (degree_bound_implies_two_mul_add_lt q m (rj k).natDegree (by linarith)
          (hdeg k hk).1)
        (degree_bound_implies_two_mul_add_lt q m (sj k).natDegree (by linarith)
          (hdeg k hk).2)
        (stepanov_nonzero_minimal_congruence F f ℓ c q J rj sj
          (by intro hf; simp [hf] at hf0) hsum k hk hk_min)
    by_cases hsk : sj k = 0
    · have heq' : rj k * rj k * f = 0 := by simpa [hsk] using heq
      have hr_eq_zero : rj k = 0 := by
        rcases mul_eq_zero.mp heq' with hr2 | hf
        · exact mul_self_eq_zero.mp hr2
        · exact (False.elim <| by simp [hf] at hf0)
      exact hk_nonzero.elim (fun hr => hr hr_eq_zero) (fun hs => hs hsk)
    · exact
        hnsq
          (stepanov_square_from_eq F f (rj k) (sj k) (f.eval 0)
            hf0 hsk heq)
  · intro hall
    have hsum_zero : Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        obtain ⟨hrj, hsj⟩ := hall j (Finset.mem_range.mp hj)
        simp [hrj, hsj]
    simp [hsum_zero]
