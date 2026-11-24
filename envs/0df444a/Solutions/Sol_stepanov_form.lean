-- Prove2me | solution 1 for stepanov_form
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:21:25.282383+00:00
-- url     : https://prove2.me/submissions/0fe618b0-df2f-4bee-87ec-9ece9bc00702

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
import Theorems.Thm_auxiliary_derivatives
import Theorems.Thm_hasseDerivOp_mul_Xqpow




theorem solution (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (ℓ q c J k : ℕ) (hk : k < ℓ)
    (hq : q = Fintype.card F) (hkq : k < q)
    (rj sj : ℕ → Polynomial F) :
  ∃ rjk sjk : ℕ → Polynomial F,
    (∀ j, hasseDerivOp F k (f^ℓ * (rj j)) = (rjk j) * f^(ℓ - k)) ∧
    (∀ j, hasseDerivOp F k (f^(ℓ + c) * (sj j)) = (sjk j) * f^(ℓ + c - k)) ∧
    hasseDerivOp F k
      (f^ℓ *
        (Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)))) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) :=
by
  have h_ex :
      ∀ j : ℕ, ∃ rjk_j sjk_j : Polynomial F,
        hasseDerivOp F k (f^ℓ * (rj j)) = rjk_j * f^(ℓ - k) ∧
        hasseDerivOp F k (f^(ℓ + c) * (sj j)) = sjk_j * f^(ℓ + c - k) := by
    intro j
    let d := Nat.max (rj j).natDegree (sj j).natDegree
    have hr : (rj j).natDegree ≤ d := Nat.le_max_left _ _
    have hs : (sj j).natDegree ≤ d := Nat.le_max_right _ _
    obtain ⟨rjk_j, sjk_j, hr_eq, hs_eq, -, -⟩ :=
      auxiliary_derivatives (F := F) f f.natDegree d ℓ c rfl (rj j) (sj j) hr hs k hk.le
    exact ⟨rjk_j, sjk_j, hr_eq, hs_eq⟩
  choose rjk sjk hrjk hsjk using h_ex
  refine ⟨rjk, sjk, hrjk, hsjk, ?_⟩
  have h_rewrite :
      f^ℓ *
        Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)) =
      Finset.sum (Finset.range J)
        (fun j => (f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) := by
    have h :=
      (Finset.mul_sum
        (s := Finset.range J)
        (f := fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))
        (a := f^ℓ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_deriv_sum :
      hasseDerivOp F k
        (f^ℓ *
          Finset.sum (Finset.range J)
            (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) =
      Finset.sum (Finset.range J)
        (fun j =>
          hasseDerivOp F k
            ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q))) := by
    simp [hasseDerivOp, h_rewrite, _root_.map_sum]
  have h_term :
      ∀ j : ℕ,
        hasseDerivOp F k
          ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) =
        f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q) := by
    intro j
    have h_split :
        f^ℓ * ((rj j) + (sj j) * f^c) =
          f^ℓ * (rj j) + f^(ℓ + c) * (sj j) := by
      simp [mul_add, pow_add, mul_comm, mul_left_comm]
    have hP_factor :
        hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) := by
      have h_add' :
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            hasseDerivOp F k (f^ℓ * (rj j)) +
              hasseDerivOp F k (f^(ℓ + c) * (sj j)) := by
        simp [hasseDerivOp, h_split]
      have h_basic :
          hasseDerivOp F k (f^ℓ * (rj j)) +
              hasseDerivOp F k (f^(ℓ + c) * (sj j)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) := by
        simp [hrjk j, hsjk j]
      have h_tmp :
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) :=
        h_add'.trans h_basic
      have h_exp : ℓ + c - k = c + (ℓ - k) := by
        have hℓ : ℓ = (ℓ - k) + k := (Nat.sub_add_cancel hk.le).symm
        have h_step : ℓ + c - k = ((ℓ - k) + k) + c - k := by
          have := congrArg (fun n => n + c - k) hℓ
          simpa using this
        have h' : ((ℓ - k) + k) + c - k = (ℓ - k) + c := by
          have htemp : ((ℓ - k) + k) + c = ((ℓ - k) + c) + k := by
            calc
              ((ℓ - k) + k) + c
                  = (ℓ - k) + (k + c) := by
                        simp [Nat.add_assoc]
              _ = (ℓ - k) + (c + k) := by
                        simp [Nat.add_comm]
              _ = ((ℓ - k) + c) + k := by
                        simp [Nat.add_assoc]
          calc
            ((ℓ - k) + k) + c - k
                = ((ℓ - k) + c) + k - k := by
                      simp [htemp]
            _ = (ℓ - k) + c := by
                      simp
        have h1 : ℓ + c - k = (ℓ - k) + c := h_step.trans h'
        have h2 : (ℓ - k) + c = c + (ℓ - k) := Nat.add_comm _ _
        exact h1.trans h2
      have hpow : f^(ℓ + c - k) = f^c * f^(ℓ - k) := by
        have hpow' := congrArg (fun n => f^n) h_exp
        simpa [pow_add] using hpow'
      calc
        hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) := h_tmp
        _ = (rjk j) * f^(ℓ - k) + (sjk j) * (f^c * f^(ℓ - k)) := by
              exact congrArg
                (fun t => (rjk j) * f^(ℓ - k) + (sjk j) * t) hpow
        _ = rjk j * f^(ℓ - k) + sjk j * f^c * f^(ℓ - k) := by
              simp [mul_assoc]
        _ = (rjk j + sjk j * f^c) * f^(ℓ - k) := by
              simp [add_mul, mul_assoc]
        _ = f^(ℓ - k) * (rjk j + sjk j * f^c) := by
              ac_rfl
    have h_prod :=
      hasseDerivOp_mul_Xqpow (F := F) (q := q) (k := k)
        (hq := hq) (hkq := hkq)
        (P := f^ℓ * ((rj j) + (sj j) * f^c)) (j := j)
    calc
      hasseDerivOp F k
          ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) =
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) *
            (Polynomial.X)^(j*q) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_prod
      _ = f^(ℓ - k) * (rjk j + sjk j * f^c) * (Polynomial.X)^(j*q) := by
            simp [hP_factor]
      _ = f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q) := by
            ac_rfl
  have h_deriv_explicit :
      hasseDerivOp F k
        (f^ℓ *
          Finset.sum (Finset.range J)
            (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) =
      Finset.sum (Finset.range J)
        (fun j =>
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
    simpa [h_term] using h_deriv_sum
  have h_factor :
      Finset.sum (Finset.range J)
        (fun j =>
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
    have h1 :
        Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
        Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * (((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [mul_assoc]
    have h_mul_sum :=
      (Finset.mul_sum
        (s := Finset.range J)
        (f :=
          fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))
        (a := f^(ℓ - k)))
    calc
      Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
          Finset.sum (Finset.range J)
            (fun j =>
              f^(ℓ - k) * (((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))) := h1
      _ = f^(ℓ - k) *
            Finset.sum (Finset.range J)
              (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
            simpa using h_mul_sum.symm
  exact h_deriv_explicit.trans h_factor
