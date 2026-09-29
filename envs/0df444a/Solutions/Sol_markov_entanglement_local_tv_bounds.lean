-- Prove2me | solution 1 for markov_entanglement_local_tv_bounds
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-07-18T15:20:55.58186+00:00
-- url     : https://prove2.me/submissions/893fa0c2-03d0-43fe-82e6-e94581c2a12b

import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

private theorem localA_bound
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    [Nonempty SA] [Nonempty SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ)
    (μ : SA × SB → ℝ) (hμpos : ∀ p, 0 < μ p)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A : IsLocalTransitionA P_AB μ P_true_A)
    (P_A : Matrix SA SA ℝ) :
    tvDist P_true_A P_A ≤ agentTVDistA P_AB P_A := by
  classical
  unfold tvDist
  apply ciSup_le
  intro a
  have hm : 0 < marginalA μ a := by
    unfold marginalA
    exact Finset.sum_pos (fun b _ => hμpos (a, b)) Finset.univ_nonempty
  have hrow (b : SB) :
      (1 / 2 : ℝ) * ∑ j : SA, |(∑ b' : SB, P_AB (a, b) (j, b')) - P_A a j| ≤
        agentTVDistA P_AB P_A := by
    unfold agentTVDistA
    exact le_ciSup (f := fun p : SA × SB =>
      (1 / 2 : ℝ) * ∑ j : SA, |(∑ b' : SB, P_AB p (j, b')) - P_A p.1 j|)
      (Finite.bddAbove_range _) (a, b)
  have hdiff (j : SA) :
      marginalA μ a * (P_true_A a j - P_A a j) =
        ∑ b : SB, μ (a, b) * ((∑ b' : SB, P_AB (a, b) (j, b')) - P_A a j) := by
    calc
      marginalA μ a * (P_true_A a j - P_A a j) =
          marginalA μ a * P_true_A a j - marginalA μ a * P_A a j := by ring
      _ = (∑ b : SB, μ (a, b) * (∑ b' : SB, P_AB (a, b) (j, b'))) -
          marginalA μ a * P_A a j := by rw [hP_true_A]
      _ = ∑ b : SB, μ (a, b) * ((∑ b' : SB, P_AB (a, b) (j, b')) - P_A a j) := by
        unfold marginalA
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        ring
  apply (mul_le_mul_iff_of_pos_left hm).mp
  calc
    marginalA μ a * ((1 / 2 : ℝ) * ∑ j : SA, |P_true_A a j - P_A a j|) =
        (1 / 2 : ℝ) * ∑ j : SA, |marginalA μ a * (P_true_A a j - P_A a j)| := by
      calc
        marginalA μ a * ((1 / 2 : ℝ) * ∑ j : SA, |P_true_A a j - P_A a j|) =
            (1 / 2 : ℝ) * (marginalA μ a * ∑ j : SA, |P_true_A a j - P_A a j|) := by ring
        _ = (1 / 2 : ℝ) * ∑ j : SA, marginalA μ a * |P_true_A a j - P_A a j| := by
          rw [Finset.mul_sum]
        _ = (1 / 2 : ℝ) * ∑ j : SA, |marginalA μ a * (P_true_A a j - P_A a j)| := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_mul, abs_of_pos hm]
    _ = (1 / 2 : ℝ) * ∑ j : SA,
        |∑ b : SB, μ (a, b) * ((∑ b' : SB, P_AB (a, b) (j, b')) - P_A a j)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdiff]
    _ ≤ (1 / 2 : ℝ) * ∑ j : SA,
        ∑ b : SB, |μ (a, b) * ((∑ b' : SB, P_AB (a, b) (j, b')) - P_A a j)| := by
      gcongr with j
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b : SB, μ (a, b) *
        ((1 / 2 : ℝ) * ∑ j : SA, |(∑ b' : SB, P_AB (a, b) (j, b')) - P_A a j|) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_pos (hμpos (a, b))]
      ring
    _ ≤ ∑ b : SB, μ (a, b) * agentTVDistA P_AB P_A := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hrow b) (le_of_lt (hμpos (a, b)))
    _ = marginalA μ a * agentTVDistA P_AB P_A := by
      unfold marginalA
      rw [Finset.sum_mul]

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (hP_AB : IsTransitionMatrix P_AB)
    (μ : SA × SB → ℝ) (hμ : IsPositiveDist μ)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A_tm : IsTransitionMatrix P_true_A)
    (hP_true_A : IsLocalTransitionA P_AB μ P_true_A)
    (P_true_B : Matrix SB SB ℝ) (hP_true_B_tm : IsTransitionMatrix P_true_B)
    (hP_true_B : IsLocalTransitionB P_AB μ P_true_B)
    (P_A : Matrix SA SA ℝ) (hP_A_tm : IsTransitionMatrix P_A)
    (hP_A_opt : agentTVDistA P_AB P_A = entanglementA P_AB)
    (P_B : Matrix SB SB ℝ) (hP_B_tm : IsTransitionMatrix P_B)
    (hP_B_opt : agentTVDistB P_AB P_B = entanglementB P_AB) :
    tvDist P_true_A P_A ≤ entanglementA P_AB ∧
    tvDist P_true_B P_B ≤ entanglementB P_AB := by
  classical
  letI : Nonempty SA := by
    by_contra h
    haveI : IsEmpty SA := not_nonempty_iff.mp h
    have hz : (0 : ℝ) = 1 := by simpa using hμ.2
    norm_num at hz
  letI : Nonempty SB := by
    by_contra h
    haveI : IsEmpty SB := not_nonempty_iff.mp h
    have hz : (0 : ℝ) = 1 := by simpa using hμ.2
    norm_num at hz
  constructor
  · rw [← hP_A_opt]
    exact localA_bound P_AB μ hμ.1 P_true_A hP_true_A P_A
  · let P_BA : Matrix (SB × SA) (SB × SA) ℝ := fun p q => P_AB (p.2, p.1) (q.2, q.1)
    let μBA : SB × SA → ℝ := fun p => μ (p.2, p.1)
    have hlocal : IsLocalTransitionA P_BA μBA P_true_B := by
      intro b b'
      simpa [P_BA, μBA, marginalA, marginalB] using hP_true_B b b'
    have hraw : tvDist P_true_B P_B ≤ agentTVDistA P_BA P_B :=
      localA_bound P_BA μBA (fun p => hμ.1 (p.2, p.1)) P_true_B hlocal P_B
    have hdist : agentTVDistA P_BA P_B = agentTVDistB P_AB P_B := by
      apply le_antisymm
      · unfold agentTVDistA agentTVDistB
        apply ciSup_le
        intro p
        simpa [P_BA] using
          (le_ciSup (f := fun q : SA × SB =>
            (1 / 2 : ℝ) * ∑ j : SB, |(∑ a : SA, P_AB q (a, j)) - P_B q.2 j|)
            (Finite.bddAbove_range _) (p.2, p.1))
      · unfold agentTVDistA agentTVDistB
        apply ciSup_le
        intro p
        simpa [P_BA] using
          (le_ciSup (f := fun q : SB × SA =>
            (1 / 2 : ℝ) * ∑ j : SB, |(∑ a : SA, P_BA q (j, a)) - P_B q.1 j|)
            (Finite.bddAbove_range _) (p.2, p.1))
    rw [← hP_B_opt, ← hdist]
    exact hraw
