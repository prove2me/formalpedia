-- Prove2me | solution 1 for markov_entanglement_decomposition_error
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-07-18T15:11:42.408211+00:00
-- url     : https://prove2.me/submissions/6b98d8bb-8f29-4008-af0e-640a9331c95d

import Theorems.Thm_markov_entanglement_local_tv_bounds
import Theorems.Thm_markov_entanglement_bellman_q_error_of_local_tv

open scoped BigOperators
open MarkovEntanglement

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (hP_AB : IsTransitionMatrix P_AB)
    (μ : SA × SB → ℝ) (hμ : IsPositiveDist μ) (hμStat : IsStationary P_AB μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r_A : SA → ℝ) (r_B : SB → ℝ) (rAmax rBmax : ℝ)
    (hrAmax : 0 ≤ rAmax) (hrBmax : 0 ≤ rBmax)
    (hrA : ∀ a, |r_A a| ≤ rAmax) (hrB : ∀ b, |r_B b| ≤ rBmax)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A_tm : IsTransitionMatrix P_true_A)
    (hP_true_A : IsLocalTransitionA P_AB μ P_true_A)
    (P_true_B : Matrix SB SB ℝ) (hP_true_B_tm : IsTransitionMatrix P_true_B)
    (hP_true_B : IsLocalTransitionB P_AB μ P_true_B)
    (Q_AB : SA × SB → ℝ) (hQ_AB : IsBellmanQ P_AB (fun p => r_A p.1 + r_B p.2) γ Q_AB)
    (Q_true_A : SA → ℝ) (hQ_true_A : IsBellmanQ P_true_A r_A γ Q_true_A)
    (Q_true_B : SB → ℝ) (hQ_true_B : IsBellmanQ P_true_B r_B γ Q_true_B)
    (P_A : Matrix SA SA ℝ) (hP_A_tm : IsTransitionMatrix P_A)
    (hP_A_opt : agentTVDistA P_AB P_A = entanglementA P_AB)
    (P_B : Matrix SB SB ℝ) (hP_B_tm : IsTransitionMatrix P_B)
    (hP_B_opt : agentTVDistB P_AB P_B = entanglementB P_AB) :
    tvDist P_true_A P_A ≤ entanglementA P_AB ∧
    tvDist P_true_B P_B ≤ entanglementB P_AB ∧
    (⨆ p : SA × SB, |Q_AB p - (Q_true_A p.1 + Q_true_B p.2)|) ≤
      4 * γ * (entanglementA P_AB * rAmax + entanglementB P_AB * rBmax) / (1 - γ) ^ 2 := by
  have hTV := markov_entanglement_local_tv_bounds P_AB hP_AB μ hμ
    P_true_A hP_true_A_tm hP_true_A P_true_B hP_true_B_tm hP_true_B
    P_A hP_A_tm hP_A_opt P_B hP_B_tm hP_B_opt
  refine ⟨hTV.1, hTV.2, ?_⟩
  exact markov_entanglement_bellman_q_error_of_local_tv
    P_AB hP_AB γ hγ0 hγ1 r_A r_B rAmax rBmax hrAmax hrBmax hrA hrB
    P_true_A hP_true_A_tm P_true_B hP_true_B_tm Q_AB hQ_AB
    Q_true_A hQ_true_A Q_true_B hQ_true_B P_A hP_A_tm hP_A_opt
    P_B hP_B_tm hP_B_opt hTV.1 hTV.2
