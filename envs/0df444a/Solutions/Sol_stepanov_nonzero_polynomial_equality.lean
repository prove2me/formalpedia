-- Prove2me | solution 1 for stepanov_nonzero_polynomial_equality
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:19:11.827984+00:00
-- url     : https://prove2.me/submissions/08194eac-6569-40c3-adc9-1107b26994b9

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

section












lemma stepanov_nonzero_frobenius_mod (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (q : ℕ) (hq : q = Fintype.card F) :
    Polynomial.X ^ q ∣ (f ^ q - Polynomial.C (f.eval 0)) :=
by
  rw [show f ^ q = Polynomial.expand F q f from
        by simpa [hq] using (FiniteField.expand_card f).symm,
      Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub,
      Polynomial.coeff_expand
        (by simpa [hq] using (Fintype.card_pos (α := F)))]
  by_cases hd0 : d = 0
  · subst hd0
    simp [Polynomial.eval, Polynomial.eval₂_at_zero]
  · simp [Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hd0) hd,
      hd0, Polynomial.coeff_C]











end



theorem solution
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f r s : Polynomial F) (q m c : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hc : c = (q - 1) / 2)
  (hrdeg : 2 * r.natDegree + m < q) (hsdeg : 2 * s.natDegree + m < q)
  (hcong : Polynomial.X ^ q ∣ (r + s * f ^ c)) :
  r * r * f = s * s * Polynomial.C (f.eval 0) :=
by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := by
    refine (Nat.odd_iff.mpr ?_)
    simpa [hq] using
      (FiniteField.odd_card_of_char_ne_two (F := F) hF)
  have h2c1 : 2 * c + 1 = q := by
    have hq_pos : 0 < q := by
      simpa [hq] using (Fintype.card_pos (α := F))
    have h2_dvd : 2 ∣ q - 1 := by
      refine ⟨k, ?_⟩
      have := congrArg (fun n => n - 1) hk
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have h2c : 2 * c = q - 1 := by
      simpa [hc, Nat.mul_comm] using
        (Nat.div_two_mul_two_of_even ((even_iff_two_dvd).2 h2_dvd))
    simpa [h2c, Nat.add_comm] using
      (Nat.sub_add_cancel (Nat.succ_le_of_lt hq_pos))
  have hdiv1 : Polynomial.X ^ q ∣ r * r - (s * f ^ c) * (s * f ^ c) := by
    have htmp : Polynomial.X ^ q ∣ (r + s * f ^ c) * (r - s * f ^ c) :=
      dvd_mul_of_dvd_left hcong (r - s * f ^ c)
    have hdsq :
        (r + s * f ^ c) * (r - s * f ^ c) =
          r * r - (s * f ^ c) * (s * f ^ c) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using
        (mul_self_sub_mul_self (a := r) (b := s * f ^ c)).symm
    simpa [hdsq] using htmp
  have hdiv2 : Polynomial.X ^ q ∣ r * r * f - s * s * f ^ (2 * c + 1) := by
    have htmp : Polynomial.X ^ q ∣ f * (r * r - (s * f ^ c) * (s * f ^ c)) :=
      dvd_mul_of_dvd_right hdiv1 f
    have hpow : f ^ c * f ^ c * f = f ^ (2 * c + 1) := by
      have : f ^ c * f ^ c * f = f ^ (c + c + 1) := by
        simp [pow_add, pow_succ, mul_comm]
      simpa [two_mul, Nat.add_assoc] using this
    have hrewrite :
        f * (r * r - (s * f ^ c) * (s * f ^ c)) =
          r * r * f - s * s * f ^ (2 * c + 1) := by
      calc
        f * (r * r - (s * f ^ c) * (s * f ^ c))
            = f * (r * r) - f * ((s * f ^ c) * (s * f ^ c)) := by
                simp [mul_sub]
        _ = r * r * f - s * s * (f ^ c * f ^ c) * f := by
                simp [mul_comm, mul_left_comm, mul_assoc]
        _ = r * r * f - s * s * (f ^ c * f ^ c * f) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
        _ = r * r * f - s * s * f ^ (2 * c + 1) := by
                simp [hpow, mul_comm, mul_assoc]
    simpa [hrewrite] using htmp
  have hdiv3 : Polynomial.X ^ q ∣
      s * s * f ^ q - s * s * Polynomial.C (f.eval 0) := by
    simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using
      (dvd_mul_of_dvd_right
        (stepanov_nonzero_frobenius_mod (F := F) (f := f) (q := q) hq) (s * s))
  have hdiv_final : Polynomial.X ^ q ∣
      r * r * f - s * s * Polynomial.C (f.eval 0) := by
    have hdiv2' : Polynomial.X ^ q ∣ r * r * f - s * s * f ^ q := by
      simpa [h2c1] using hdiv2
    have h := dvd_add hdiv2' hdiv3
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hdeg_r2f_lt : (r * r * f).natDegree < q := by
    refine lt_of_le_of_lt ?_ hrdeg
    refine
      (Polynomial.natDegree_mul_le (p := r * r) (q := f)).trans ?_
    have h2 : (r * r).natDegree ≤ 2 * r.natDegree := by
      simpa [two_mul] using (Polynomial.natDegree_mul_le (p := r) (q := r))
    simpa [hfdeg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add_right h2 m
  have hdeg_s2C_lt :
      (s * s * Polynomial.C (f.eval 0)).natDegree < q := by
    have h2s_lt_q : 2 * s.natDegree < q := by
      have :=
        lt_of_le_of_lt
          (Nat.add_le_add_left (Nat.zero_le m) (2 * s.natDegree)) hsdeg
      simpa using this
    refine lt_of_le_of_lt ?_ h2s_lt_q
    refine
      (Polynomial.natDegree_mul_le (p := s * s)
        (q := Polynomial.C (f.eval 0))).trans ?_
    have h2 : (s * s).natDegree ≤ 2 * s.natDegree := by
      simpa [two_mul] using (Polynomial.natDegree_mul_le (p := s) (q := s))
    have hC : (Polynomial.C (f.eval 0 : F)).natDegree = 0 := by simp
    simpa [hC, Nat.add_comm] using h2
  have hdeg_diff_lt :
      (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree < q := by
    have hdeg_diff_le :
        (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree ≤
          max (r * r * f).natDegree
            (s * s * Polynomial.C (f.eval 0)).natDegree := by
      simpa [sub_eq_add_neg] using
        (Polynomial.natDegree_add_le (p := r * r * f)
          (q := -(s * s * Polynomial.C (f.eval 0))))
    exact
      lt_of_le_of_lt hdeg_diff_le
        (max_lt_iff.mpr ⟨hdeg_r2f_lt, hdeg_s2C_lt⟩)
  have hdiff_zero : r * r * f - s * s * Polynomial.C (f.eval 0) = 0 := by
    by_contra hne
    have hdeg_ge :
        q ≤ (r * r * f - s * s * Polynomial.C (f.eval 0)).natDegree := by
      have h :=
        Polynomial.natDegree_le_of_dvd (p := (Polynomial.X ^ q : Polynomial F))
          (q := r * r * f - s * s * Polynomial.C (f.eval 0)) hdiv_final hne
      simpa using h
    exact (not_lt_of_ge hdeg_ge hdeg_diff_lt)
  exact sub_eq_zero.mp hdiff_zero
