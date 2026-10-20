-- Prove2me | solution 1 for p2m_dual_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:47:02.928404+00:00
-- url     : https://prove2.me/submissions/de53c178-1635-4512-aff2-10015d4d3a6f

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_stepLength_le_one
import Theorems.Thm_p2m_dual_step_contraction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k)) :
    ∀ k ≤ K, norm1 (dualInfeas A c (s k)) ≤ (1 - t) ^ k * norm1 (dualInfeas A c (s 0)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp
  | succ k ih =>
      intro hk
      have hkprev : k ≤ K := le_trans (Nat.le_succ k) hk
      have hprev := ih hkprev
      have hcontract := p2m_dual_step_contraction A b c δ r t hδ0 hδ1 hr0 hr1
        (s k) (d k) (s (k + 1)) (hstep k hkprev) (hθ k hkprev)
      have hcoef : 0 ≤ 1 - t := by
        have := p2m_stepLength_le_one r (s k) (d k)
        linarith [hθ k hkprev]
      calc
        norm1 (dualInfeas A c (s (k + 1))) ≤
            (1 - t) * norm1 (dualInfeas A c (s k)) := hcontract
        _ ≤ (1 - t) * ((1 - t) ^ k * norm1 (dualInfeas A c (s 0))) :=
            mul_le_mul_of_nonneg_left hprev hcoef
        _ = (1 - t) ^ (k + 1) * norm1 (dualInfeas A c (s 0)) := by rw [pow_succ]; ring
