-- Prove2me | solution 1 for hasse_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:19:01.491278+00:00
-- url     : https://prove2.me/submissions/af79c595-986c-43cb-9b77-f6934abd7adf

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




theorem solution (F : Type*) [Field F] (f : Polynomial F) (a : F) (ℓ : ℕ)
    (hvan : ∀ k < ℓ, (hasseDerivOp F k f).eval a = 0) :
    (Polynomial.X - Polynomial.C a)^ℓ ∣ f :=
by
  set t : Polynomial F := Polynomial.taylor a f
  have hcoeff0 : ∀ k < ℓ, t.coeff k = 0 := by
    intro k hk
    simpa [t, Polynomial.taylor_coeff, hasseDerivOp] using hvan k hk
  have hfact :
      t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ i) =
        (Polynomial.X - Polynomial.C a) ^ ℓ *
          t.sum (fun i c =>
            Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ (i - ℓ)) := by
    simp [Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hle : ℓ ≤ i := by
      by_contra h
      have : t.coeff i = 0 := hcoeff0 i (Nat.lt_of_not_ge h)
      exact (Polynomial.mem_support_iff.mp hi) this
    calc
      Polynomial.C (t.coeff i) * (Polynomial.X - Polynomial.C a) ^ i
          = (Polynomial.X - Polynomial.C a) ^ i *
              Polynomial.C (t.coeff i) := by
                simp [mul_comm]
      _ = (Polynomial.X - Polynomial.C a) ^ (ℓ + (i - ℓ)) *
              Polynomial.C (t.coeff i) := by
                simp [Nat.add_sub_of_le hle]
      _ = (Polynomial.X - Polynomial.C a) ^ ℓ *
              (Polynomial.C (t.coeff i) *
                (Polynomial.X - Polynomial.C a) ^ (i - ℓ)) := by
                simp [pow_add, mul_comm, mul_assoc]
  refine ⟨t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ (i - ℓ)), ?_⟩
  have hf :
      f =
        t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ i) := by
    simpa [t] using (Polynomial.sum_taylor_eq (R := F) f a).symm
  exact hf.trans hfact
