-- Prove2me | solution 1 for hasseDerivOp_X_sub_C_pow
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:23:32.759806+00:00
-- url     : https://prove2.me/submissions/2554770c-1896-4bcb-8925-611d2e8d6966

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




theorem solution (F : Type*) [Field F]
    (k r : ℕ) (hk : k ≤ r) :
    ∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k) :=
by
  intro a
  ext n
  have hL :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        ((n + k).choose k : F) *
          ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) := by
    simpa [hasseDerivOp] using
      (Polynomial.hasseDeriv_coeff (k := k)
        (f := (Polynomial.X - Polynomial.C a) ^ r) (n := n))
  have hcoeff_pow :
      ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) =
        (-a) ^ (r - (n + k)) * (Nat.choose r (n + k) : F) := by
    simpa [sub_eq_add_neg] using
      (Polynomial.coeff_X_add_C_pow (R := F) (-a) r (n + k))
  have hcoeff_pow2 :
      ((Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
        (-a) ^ ((r - k) - n) * (Nat.choose (r - k) n : F) := by
    simpa [sub_eq_add_neg] using
      (Polynomial.coeff_X_add_C_pow (R := F) (-a) (r - k) n)
  have hL' :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        (-a) ^ (r - (n + k)) *
          (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) := by
    calc
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
          ((n + k).choose k : F) *
            ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) := hL
      _ = ((n + k).choose k : F) *
            ((-a) ^ (r - (n + k)) * (Nat.choose r (n + k) : F)) := by
            simp [hcoeff_pow]
      _ = (-a) ^ (r - (n + k)) *
            (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) := by
            ring
  have hR' :
      (Polynomial.C (Nat.choose r k : F) *
          (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
        (-a) ^ (r - (n + k)) *
          ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
    calc
      (Polynomial.C (Nat.choose r k : F) *
            (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
          (Nat.choose r k : F) *
            ((Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n := by
            simp
      _ = (Nat.choose r k : F) *
            ((-a) ^ ((r - k) - n) * (Nat.choose (r - k) n : F)) := by
            simp [hcoeff_pow2]
      _ = (Nat.choose r k : F) *
            ((-a) ^ (r - (n + k)) * (Nat.choose (r - k) n : F)) := by
            have : (r - k) - n = r - (n + k) := by
              simp [Nat.add_comm, Nat.sub_sub]
            simp [this]
      _ = (-a) ^ (r - (n + k)) *
            ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
            ring
  have hscalar :
      (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) =
        (Nat.choose r k : F) * (Nat.choose (r - k) n : F) := by
    by_cases hnk : n + k ≤ r
    · have hsk : k ≤ n + k := Nat.le_add_left k n
      have h_nat :
          (Nat.choose r (n + k) * Nat.choose (n + k) k : ℕ) =
            Nat.choose r k * Nat.choose (r - k) n := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.choose_mul (n := r) (k := n + k) (s := k) hsk)
      have h_natF :
          ((Nat.choose r (n + k) * Nat.choose (n + k) k : ℕ) : F) =
            (Nat.choose r k * Nat.choose (r - k) n : ℕ) := by
        exact congrArg (fun x : ℕ => (x : F)) h_nat
      have h_main :
          (Nat.choose r (n + k) : F) * (Nat.choose (n + k) k : F) =
            (Nat.choose r k : F) * (Nat.choose (r - k) n : F) := by
        simpa [Nat.cast_mul] using h_natF
      simpa [mul_comm] using h_main
    · have hlt : r < n + k := Nat.lt_of_not_ge hnk
      have hlt' : r - k < n :=
        (add_lt_add_iff_right (a := k)).1
          (by simpa [Nat.sub_add_cancel hk] using hlt)
      simp [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hlt']
  have hmid :
      (-a) ^ (r - (n + k)) *
        (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) =
      (-a) ^ (r - (n + k)) *
        ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
    exact congrArg (fun x => (-a) ^ (r - (n + k)) * x) hscalar
  have hcoeff_eq :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        (Polynomial.C (Nat.choose r k : F) *
          (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n :=
    (hL'.trans hmid).trans hR'.symm
  simpa using hcoeff_eq
