-- Prove2me | solution 1 for mme_empirical_word_probability_and_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:04:10.53603+00:00
-- url     : https://prove2.me/submissions/8eae9e00-5b35-4cd2-9ece-dd72d8fe0f29

import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_mme_modern_entropy_data

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

namespace MME.EmpiricalWord

private theorem card_composite_fiber
    {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (g : A → B) (q : B → C) (c : C) :
    Fintype.card {a : A // q (g a) = c} =
      ∑ b : {b : B // q b = c},
        Fintype.card {a : A // g a = b.1} := by
  classical
  let e : {a : A // q (g a) = c} ≃
      Σ b : {b : B // q b = c}, {a : A // g a = b.1} := {
    toFun a := ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
    invFun a := ⟨a.2.1, by rw [a.2.2, a.1.2]⟩
    left_inv a := by ext; rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

theorem proof
    {R I : Type*} [Fintype R] [DecidableEq R] [DecidableEq I]
    (n : ℕ) (hn : 0 < n) (f : Fin n → R) (coord : R → I) :
    let p : R → ℝ := fun r ↦
      (Fintype.card {t : Fin n // f t = r} : ℝ) / (n : ℝ)
    (∀ r, 0 ≤ p r) ∧
      (∑ r, p r = 1) ∧
      ∀ i, mme_modern_marginal coord p i =
        (Fintype.card {t : Fin n // coord (f t) = i} : ℝ) / (n : ℝ) := by
  classical
  dsimp only
  have hsum : ∑ r, Fintype.card {t : Fin n // f t = r} = n := by
    calc
      ∑ r, Fintype.card {t : Fin n // f t = r} =
          Fintype.card (Σ r : R, {t : Fin n // f t = r}) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (Fin n) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv f)
      _ = n := Fintype.card_fin n
  refine ⟨fun r ↦ by positivity, ?_, ?_⟩
  · rw [← Finset.sum_div, ← Nat.cast_sum, hsum]
    exact div_self (by exact_mod_cast hn.ne')
  · intro i
    unfold mme_modern_marginal
    rw [← Finset.sum_div, ← Nat.cast_sum,
      ← card_composite_fiber f coord i]

end MME.EmpiricalWord

theorem solution
    {R I : Type*} [Fintype R] [DecidableEq R] [DecidableEq I]
    (n : ℕ) (hn : 0 < n) (f : Fin n → R) (coord : R → I) :
    let p : R → ℝ := fun r ↦
      (Fintype.card {t : Fin n // f t = r} : ℝ) / (n : ℝ)
    (∀ r, 0 ≤ p r) ∧
      (∑ r, p r = 1) ∧
      ∀ i, mme_modern_marginal coord p i =
        (Fintype.card {t : Fin n // coord (f t) = i} : ℝ) / (n : ℝ) :=
  MME.EmpiricalWord.proof n hn f coord
