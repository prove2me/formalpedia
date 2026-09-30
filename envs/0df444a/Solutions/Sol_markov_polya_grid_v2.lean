-- Prove2me | solution 1 for markov_polya_grid_v2
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:31:03.096348+00:00
-- url     : https://prove2.me/submissions/c6e9063a-2af8-4586-b1bb-3d55ed75fc82

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace MarkovGridCounterexample

def denominator : ℤ := 17420181261730140817797573414006060306035097600000

def numerator (t : ℤ) : ℤ :=
  (0 + t * (-9971411306782352126547538802203688304818936064000 + t * (1805670176749440845004197153469585983723594544000 + t * (-113674936632661253038168342523813961822677608320 + t * (3568868446157488858790641933079905994849308824 + t * (-65099128971846497919183024886235137843526140 + t * (746673854613436394084075214984302022773566 + t * (-5610452107537779326103033449915646183609 + t * (28034844341127376477087258158558865269 + t * (-92332003101575728196449781732078442 + t * (192554124114635494179078480984108 + t * (-230427350834140577504889659489 + t * 120540902539766429535636233))))))))))))

open Polynomial in
noncomputable def P : Polynomial ℝ :=
  (C (0) + X * (C (-9971411306782352126547538802203688304818936064000) + X * (C (1805670176749440845004197153469585983723594544000) + X * (C (-113674936632661253038168342523813961822677608320) + X * (C (3568868446157488858790641933079905994849308824) + X * (C (-65099128971846497919183024886235137843526140) + X * (C (746673854613436394084075214984302022773566) + X * (C (-5610452107537779326103033449915646183609) + X * (C (28034844341127376477087258158558865269) + X * (C (-92332003101575728196449781732078442) + X * (C (192554124114635494179078480984108) + X * (C (-230427350834140577504889659489) + X * C (120540902539766429535636233)))))))))))))

noncomputable def Q : Polynomial ℝ :=
  P * Polynomial.C ((denominator : ℝ)⁻¹)

lemma denominator_pos : (0 : ℝ) < denominator := by norm_num [denominator]

lemma eval_nat (t : ℕ) : Q.eval (t : ℝ) = (numerator (t : ℤ) : ℝ) / denominator := by
  simp only [Q, P, numerator, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]
  push_cast
  ring

lemma degree_bound : Q.natDegree ≤ 12 := by
  unfold Q P
  compute_degree!

lemma integer_bounds : ∀ t : Fin 321,
    -denominator ≤ numerator t.val ∧ numerator t.val ≤ denominator := by
  decide

lemma grid_bound (t : ℕ) (ht : t ≤ 320) : |Q.eval (t : ℝ)| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := integer_bounds ⟨t, by omega⟩
  rw [eval_nat, abs_le]
  constructor
  · apply (le_div_iff₀ denominator_pos).2
    norm_num only [neg_one_mul]
    exact_mod_cast hlo
  · apply (div_le_iff₀ denominator_pos).2
    norm_num only [one_mul]
    exact_mod_cast hhi

lemma at_zero : Q.eval 0 = 0 := by
  simpa [numerator] using eval_nat 0

lemma derivative_at_endpoint : Q.derivative.eval 320 =
    (312777602295227347957506257700196313 : ℝ) / 347517334816773659433743013107135040 := by
  norm_num [Q, P, denominator, Polynomial.derivative_mul, Polynomial.derivative_add]

lemma derivative_too_large : (9 : ℝ) / 10 < |Q.derivative.eval 320| := by
  rw [derivative_at_endpoint]
  norm_num

end MarkovGridCounterexample

theorem solution : ¬ (∀ {b : ℕ}, 1 ≤ b → ∀ Q : Polynomial ℝ, ∀ {d : ℕ},
    Q.natDegree ≤ d → Q.eval 0 = 0 →
    (∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) →
    2 * d^2 ≤ b → ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 / (b : ℝ)) := by
  intro h
  have hbound := h (b := 320) (by norm_num) MarkovGridCounterexample.Q
    (d := 12) MarkovGridCounterexample.degree_bound MarkovGridCounterexample.at_zero
    MarkovGridCounterexample.grid_bound (by norm_num) 320 (by norm_num) (by norm_num)
  have hbad := MarkovGridCounterexample.derivative_too_large
  norm_num at hbound
  exact (not_le_of_gt hbad) hbound

#print axioms solution

