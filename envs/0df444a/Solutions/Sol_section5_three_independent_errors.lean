-- Prove2me | solution 1 for section5_three_independent_errors
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:00.799802+00:00
-- url     : https://prove2.me/submissions/cce835f5-137e-4ee9-b855-64b44cc84463

import Mathlib
section
set_option autoImplicit false

theorem section5_majority_three_bernoulli_bound (p1 p2 p3 : ℝ)
    (h1 : 0 ≤ p1) (h1' : p1 ≤ 1/4)
    (h2 : 0 ≤ p2) (h2' : p2 ≤ 1/4)
    (h3 : 0 ≤ p3) (h3' : p3 ≤ 1/4) :
    p1*p2*(1-p3) + p1*(1-p2)*p3 + (1-p1)*p2*p3 + p1*p2*p3 ≤ 5/32 := by
  have hp1 : 0 ≤ p2+p3-2*p2*p3 := by
    have hleft : 0 ≤ p2*(1-p3) := mul_nonneg h2 (by linarith)
    have hright : 0 ≤ p3*(1-p2) := mul_nonneg h3 (by linarith)
    nlinarith
  have hp2 : 0 ≤ (1/4:ℝ)+p3-2*(1/4)*p3 := by linarith
  have hh1 : (p1-1/4)*(p2+p3-2*p2*p3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hp1
  have hh2 : (p2-1/4)*((1/4:ℝ)+p3-2*(1/4)*p3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hp2
  nlinarith







end
set_option autoImplicit false
theorem solution {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α → ℝ) (q : β → ℝ) (r : γ → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b) (hr : ∀ c, 0 ≤ r c)
    (hpt : ∑ a, p a = 1) (hqt : ∑ b, q b = 1) (hrt : ∑ c, r c = 1)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hP : ∑ a ∈ Finset.univ.filter P, p a ≤ 1/4)
    (hQ : ∑ b ∈ Finset.univ.filter Q, q b ≤ 1/4)
    (hR : ∑ c ∈ Finset.univ.filter R, r c ≤ 1/4) :
    (∑ a : α, ∑ b : β, ∑ c : γ,
      if (P a ∧ Q b) ∨ (P a ∧ R c) ∨ (Q b ∧ R c) then p a*q b*r c else 0) ≤ 5/32 := by
  classical
  let p1 := ∑ a ∈ Finset.univ.filter P, p a
  let p2 := ∑ b ∈ Finset.univ.filter Q, q b
  let p3 := ∑ c ∈ Finset.univ.filter R, r c
  have hsel1 : (∑ a : α, if P a then p a else 0) = p1 := by
    dsimp [p1]
    exact (Finset.sum_filter _ _).symm
  have hsel2 : (∑ b : β, if Q b then q b else 0) = p2 := by
    dsimp [p2]
    exact (Finset.sum_filter _ _).symm
  have hsel3 : (∑ c : γ, if R c then r c else 0) = p3 := by
    dsimp [p3]
    exact (Finset.sum_filter _ _).symm
  have hcomp (X : Type) [Fintype X] (f : X → ℝ) (T : X → Prop) [DecidablePred T]
      (ht : ∑ x, f x = 1) :
      (∑ x : X, if T x then f x else 0) + (∑ x : X, if ¬T x then f x else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert ht using 1
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : T x <;> simp [h]
  have hevent (a : α) (b : β) (c : γ) :
      (if (P a ∧ Q b) ∨ (P a ∧ R c) ∨ (Q b ∧ R c) then p a*q b*r c else 0) =
      (if P a then p a else 0)*(if Q b then q b else 0)*(if ¬R c then r c else 0) +
      (if P a then p a else 0)*(if ¬Q b then q b else 0)*(if R c then r c else 0) +
      (if ¬P a then p a else 0)*(if Q b then q b else 0)*(if R c then r c else 0) +
      (if P a then p a else 0)*(if Q b then q b else 0)*(if R c then r c else 0) := by
    by_cases ha : P a <;> by_cases hb : Q b <;> by_cases hc : R c <;> simp [ha,hb,hc]
  have hn1 : (∑ a : α, if ¬P a then p a else 0) = 1-p1 := by
    have hh := hcomp α p P hpt
    rw [hsel1] at hh
    linarith only [hh]
  have hn2 : (∑ b : β, if ¬Q b then q b else 0) = 1-p2 := by
    have hh := hcomp β q Q hqt
    rw [hsel2] at hh
    linarith only [hh]
  have hn3 : (∑ c : γ, if ¬R c then r c else 0) = 1-p3 := by
    have hh := hcomp γ r R hrt
    rw [hsel3] at hh
    linarith only [hh]
  simp_rw [hevent, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [hn1,hn2,hn3,hsel1,hsel2,hsel3]
  exact section5_majority_three_bernoulli_bound p1 p2 p3
    (Finset.sum_nonneg (fun a _ => hp a)) hP
    (Finset.sum_nonneg (fun b _ => hq b)) hQ
    (Finset.sum_nonneg (fun c _ => hr c)) hR
