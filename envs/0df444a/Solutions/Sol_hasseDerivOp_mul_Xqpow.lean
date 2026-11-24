-- Prove2me | solution 1 for hasseDerivOp_mul_Xqpow
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:51:33.846263+00:00
-- url     : https://prove2.me/submissions/76c3c0ea-cd84-4fc6-ba0b-99d012eff735

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
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




theorem solution
  (F : Type*) [Field F] [Fintype F]
  (q k : ℕ) (hq : q = Fintype.card F) (hkq : k < q)
  (P : Polynomial F) (j : ℕ) :
  hasseDerivOp F k (P * (Polynomial.X : Polynomial F)^(j * q)) =
    hasseDerivOp F k P * (Polynomial.X : Polynomial F)^(j * q) :=
by
  have choose_mul_card_pow_cast_eq_zero
      (q j i : ℕ) (hq : q = Fintype.card F)
      (hi_pos : 0 < i) (hi_lt : i < q) :
      (Nat.choose (j * q) i : F) = 0 := by
    have hfrob :
        (1 + (Polynomial.X : Polynomial F)) ^ q =
          (1 : Polynomial F) ^ q +
            (Polynomial.X : Polynomial F) ^ q := by
      simpa [hq, FiniteField.coe_frobeniusAlgHom] using
        (FiniteField.frobeniusAlgHom F (Polynomial F)).map_add
          (1 : Polynomial F) (Polynomial.X : Polynomial F)
    have hpow :
        (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
          (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
      have h1 :
          (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
            ((1 + (Polynomial.X : Polynomial F)) ^ q) ^ j := by
        simp [pow_mul, mul_comm]
      have h2 :
          ((1 + (Polynomial.X : Polynomial F)) ^ q) ^ j =
            (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
        simpa [one_pow] using
          congrArg (fun p : Polynomial F => p ^ j) hfrob
      exact h1.trans h2
    have hcoeff_right_zero :
        ((1 + (Polynomial.X : Polynomial F) ^ q) ^ j).coeff i = 0 := by
      have h' : ∀ n : ℕ,
          ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i = 0 := by
        refine Nat.rec ?base ?step
        · have hi_ne_zero : i ≠ 0 := ne_of_gt hi_pos
          simp [pow_zero, Polynomial.coeff_one, hi_ne_zero]
        · intro n hn
          have hmul :
              (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                  (Polynomial.X : Polynomial F) ^ q).coeff i = 0 := by
            simpa [Nat.not_le.mpr hi_lt] using
              (Polynomial.coeff_mul_X_pow'
                (p := (1 + (Polynomial.X : Polynomial F) ^ q) ^ n)
                (n := q) (d := i))
          have :
              ((1 + (Polynomial.X : Polynomial F) ^ q) ^ (n.succ)).coeff i =
                ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i +
                  (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                      (Polynomial.X : Polynomial F) ^ q).coeff i := by
            simp [pow_succ, mul_add, Polynomial.coeff_add]
          simp [this, hn, hmul]
      exact h' j
    have hcoeff_left_zero :
        ((1 + (Polynomial.X : Polynomial F)) ^ (j * q)).coeff i = 0 := by
      simpa [congrArg (fun p : Polynomial F => p.coeff i) hpow.symm]
        using hcoeff_right_zero
    simpa [Polynomial.coeff_one_add_X_pow (R := F) (n := j * q) (k := i)]
      using hcoeff_left_zero

  have hasseDerivOp_X_pow_mul_card_eq_zero
      (j k : ℕ) (hq : q = Fintype.card F)
      (hk_pos : 0 < k) (hk_lt : k < q) :
      hasseDerivOp F k ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 := by
    have hchoose_zero :
        (Nat.choose (j * q) k : F) = 0 :=
      choose_mul_card_pow_cast_eq_zero q j k hq hk_pos hk_lt
    simp [hasseDerivOp, Polynomial.X_pow_eq_monomial, hchoose_zero]

  cases k with
  | zero =>
      simp [hasseDerivOp, mul_comm]
  | succ k' =>
      have hmul :
          hasseDerivOp F (Nat.succ k')
              (P * (Polynomial.X : Polynomial F) ^ (j * q)) =
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2
                  ((Polynomial.X : Polynomial F) ^ (j * q)) := by
        simpa [hasseDerivOp, mul_comm, mul_left_comm, mul_assoc] using
          (Polynomial.hasseDeriv_mul (R := F) (k := Nat.succ k')
            (f := P)
            (g := (Polynomial.X : Polynomial F) ^ (j * q)))
      have hsum :
          ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2
                  ((Polynomial.X : Polynomial F) ^ (j * q)) =
            hasseDerivOp F (Nat.succ k') P *
              (Polynomial.X : Polynomial F) ^ (j * q) := by
        have h' :
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
                hasseDerivOp F p.1 P *
                  hasseDerivOp F p.2
                    ((Polynomial.X : Polynomial F) ^ (j * q)) =
              hasseDerivOp F (Nat.succ k') P *
                hasseDerivOp F 0
                  ((Polynomial.X : Polynomial F) ^ (j * q)) := by
          refine
            Finset.sum_eq_single_of_mem
              (a := (Nat.succ k', 0))
              ?ha
              ?hothers
          · exact Finset.mem_antidiagonal.mpr (by simp)
          · intro p hp_mem hp_ne
            rcases p with ⟨a, b⟩
            change (a, b) ∈ _ at hp_mem
            change (a, b) ≠ (Nat.succ k', 0) at hp_ne
            have hsum_ab : a + b = Nat.succ k' :=
              Finset.mem_antidiagonal.mp hp_mem
            have hb_ne_zero : b ≠ 0 := by
              intro hb0
              have : a = Nat.succ k' := by
                simpa [hb0] using hsum_ab
              apply hp_ne
              ext <;> simp [this, hb0]
            have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne_zero
            have hb_le : b ≤ Nat.succ k' := by
              have : b ≤ a + b := Nat.le_add_left _ _
              simpa [hsum_ab] using this
            have hb_ltq : b < q := lt_of_le_of_lt hb_le hkq
            have hderiv_zero :
                hasseDerivOp F b
                    ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 :=
              hasseDerivOp_X_pow_mul_card_eq_zero j b hq hb_pos hb_ltq
            simp [hderiv_zero]
        simpa [hasseDerivOp] using h'
      simpa using (hmul.trans hsum)
