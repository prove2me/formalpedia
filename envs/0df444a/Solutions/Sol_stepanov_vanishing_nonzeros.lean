-- Prove2me | solution 1 for stepanov_vanishing_nonzeros
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:34:37.000849+00:00
-- url     : https://prove2.me/submissions/03e7d460-6a4f-4894-b34d-ab152b267a56

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
import Theorems.Thm_stepanov_form




theorem solution (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (ℓ q c J : ℕ) (hq : q = Fintype.card F)
  (rj sj : ℕ → Polynomial F) (a x : F) (hkq : ∀ k < ℓ, k < q) (hvan :
    ∀ k < ℓ,
    Finset.sum (Finset.range J)
      (fun j =>
        (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x
          + a *
            ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) / f ^ (ℓ + c - k)).eval x) *
          x ^ j) = 0)
  (hx_ne : f.eval x ≠ 0) (hx_pow : (f.eval x) ^ c = a) :
  ∀ k < ℓ,
  (hasseDerivOp F k
    (f ^ ℓ * (Finset.sum (Finset.range J)
      (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q))))).eval x = 0 :=
by
  intro k hk
  obtain ⟨rjk, sjk, hrjk, hsjk, h_main⟩ :=
    stepanov_form F f ℓ q c J k hk hq (hkq k hk) rj sj
  rw [h_main, Polynomial.eval_mul, mul_eq_zero]
  right
  rw [Polynomial.eval_finset_sum]
  have hx_pow_q : x ^ q = x := by simpa [hq] using FiniteField.pow_card x
  have hrjk_div j : rjk j = hasseDerivOp F k (f ^ ℓ * rj j) / f ^ (ℓ - k) := by
    simpa using
      (EuclideanDomain.eq_div_of_mul_eq_left
        (pow_ne_zero _ (fun hf0 => hx_ne (by simp [hf0])))
        (hrjk j).symm)
  have hsjk_div j :
      sjk j = hasseDerivOp F k (f ^ (ℓ + c) * sj j) / f ^ (ℓ + c - k) := by
    simpa using
      (EuclideanDomain.eq_div_of_mul_eq_left
        (pow_ne_zero _ (fun hf0 => hx_ne (by simp [hf0])))
        (hsjk j).symm)
  simp_rw [fun j =>
    show
      Polynomial.eval x ((rjk j + sjk j * f ^ c) * Polynomial.X ^ (j * q)) =
        (Polynomial.eval x (hasseDerivOp F k (f ^ ℓ * rj j) / f ^ (ℓ - k)) +
            a *
              Polynomial.eval x
                (hasseDerivOp F k (f ^ (ℓ + c) * sj j) / f ^ (ℓ + c - k))) *
          x ^ j by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        mul_comm j q, pow_mul, hx_pow_q, Polynomial.eval_add, hrjk_div j,
        hsjk_div j, hx_pow]
      ring]
  exact hvan k hk
