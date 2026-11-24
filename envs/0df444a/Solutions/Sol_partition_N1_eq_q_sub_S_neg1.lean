-- Prove2me | solution 1 for partition_N1_eq_q_sub_S_neg1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:18:56.023677+00:00
-- url     : https://prove2.me/submissions/09a77f50-fe16-4c0f-b373-7deec549f969

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovPolynomial
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
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2)
    [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) (-1))] :
    (Fintype.card
        {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
          Polynomial.eval x f ≠ 0} : ℝ)
      = (q : ℝ) -
        (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) (-1)} : ℝ) :=
by
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h1_ne_neg1 : (1 : F) ≠ -1 := by
    intro h
    have h2 : (2 : F) = 0 := by
      calc
        (2 : F) = 1 - (-1) := by ring
        _ = 1 - 1 := by rw [← h]
        _ = 0 := by ring
    exact hodd (CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2)
  let N1 :=
    Finset.univ.filter (fun x : F => (Polynomial.eval x f) ^ c = 1 ∧
      Polynomial.eval x f ≠ 0)
  let Sn1 := Finset.univ.filter (fun x : F => x ∈ S_a F f c (-1))
  have h_compl : N1 = Sn1ᶜ := by
    ext x
    simp only [N1, Sn1, Finset.mem_compl, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change ((Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0) ↔
      ¬ (Polynomial.eval x f = 0 ∨ (Polynomial.eval x f) ^ c = -1)
    rw [not_or]
    constructor
    · rintro ⟨h1, hne⟩
      refine ⟨hne, ?_⟩
      intro hm1
      exact h1_ne_neg1 (h1.symm.trans hm1)
    · intro h
      have h' : Polynomial.eval x f ≠ 0 ∧
          (Polynomial.eval x f) ^ c ≠ -1 := by
        simpa [not_or] using h
      have h_euler := FiniteField.pow_dichotomy hodd h'.1
      rw [hcard_div] at h_euler
      rcases h_euler with h1 | hm1'
      · exact ⟨h1, h'.1⟩
      · exact (h'.2 hm1').elim
  have hN1_card_real :
      (N1.card : ℝ) = (Fintype.card F : ℝ) - (Sn1.card : ℝ) := by
    have hN1_card : N1.card = Fintype.card F - Sn1.card := by
      simp [h_compl, Finset.card_compl]
    have hSn1_le : Sn1.card ≤ Fintype.card F :=
      Finset.card_le_card (Finset.subset_univ _)
    simp [hN1_card, Nat.cast_sub hSn1_le]
  have h_N1_eq :
      Fintype.card {x : F // (Polynomial.eval x f) ^ c = 1 ∧
        Polynomial.eval x f ≠ 0} = N1.card :=
    Fintype.card_subtype _
  have h_S_eq :
      Fintype.card {x : F // x ∈ S_a F f c (-1)} = Sn1.card :=
    Fintype.card_subtype _
  simp only [hc_def] at h_N1_eq h_S_eq
  convert
      (by
        simp only [h_N1_eq, h_S_eq, hN1_card_real] :
          (Fintype.card {x : F // (Polynomial.eval x f) ^
              ((Fintype.card F - 1) / 2) = 1 ∧
              Polynomial.eval x f ≠ 0} : ℝ) =
            (Fintype.card F : ℝ) -
              (Fintype.card {x : F // x ∈ S_a F f
                ((Fintype.card F - 1) / 2) (-1)} : ℝ)) using 4
