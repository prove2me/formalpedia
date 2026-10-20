-- Prove2me | solution 1 for p2m_path_primal_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:14:36.771979+00:00
-- url     : https://prove2.me/submissions/67390b12-fe24-4da4-bfc3-8d3a99a63515

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_path_stepLength_le_one
import Theorems.Thm_p2m_path_primal_step_contraction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k)) :
    ∀ k ≤ K, norm1 (primalInfeas A b (s k)) ≤ (1 - t) ^ k * norm1 (primalInfeas A b (s 0)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp
  | succ k ih =>
      intro hk
      have hkprev : k ≤ K := le_trans (Nat.le_succ k) hk
      have hprev := ih hkprev
      have hcontract := p2m_path_primal_step_contraction A b c δ r t hδ0 hδ1 hr0 hr1
        (s k) (d k) (s (k + 1)) (hstep k hkprev) (hθ k hkprev)
      have hcoef : 0 ≤ 1 - t := by
        have := p2m_path_stepLength_le_one r (s k) (d k)
        linarith [hθ k hkprev]
      calc
        norm1 (primalInfeas A b (s (k + 1))) ≤
            (1 - t) * norm1 (primalInfeas A b (s k)) := hcontract
        _ ≤ (1 - t) * ((1 - t) ^ k * norm1 (primalInfeas A b (s 0))) :=
            mul_le_mul_of_nonneg_left hprev hcoef
        _ = (1 - t) ^ (k + 1) * norm1 (primalInfeas A b (s 0)) := by rw [pow_succ]; ring
end
