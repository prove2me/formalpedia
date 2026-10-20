-- Prove2me | solution 1 for p2m_complementarity_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:05:56.587177+00:00
-- url     : https://prove2.me/submissions/417313e4-1a52-462a-876d-5b2a5b4be1e7

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_primal_decay
import Theorems.Thm_p2m_dual_decay
import Theorems.Thm_p2m_normInf_nonneg
import Theorems.Thm_p2m_complementarity_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t M : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k))
    (hx : ∀ k ≤ K, normInf (s k).x ≤ M) (hy : ∀ k ≤ K, normInf (s k).y ≤ M)
    (hone : ∀ k ≤ K,
      complementarity (s (k + 1)) ≤
        (1 - (1 - δ) * stepLength r (s k) (d k)) * complementarity (s k)
          + M * norm1 (primalInfeas A b (s k)) + M * norm1 (dualInfeas A c (s k))) :
    ∀ k, k + 1 ≤ K →
      complementarity (s (k + 1)) ≤
        (1 - t * (1 - δ)) * complementarity (s k)
          + M * (1 - t) ^ k
            * (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))) := by
  intro k hk
  have hkprev : k ≤ K := le_trans (Nat.le_succ k) hk
  have htheta := hθ k hkprev
  have hM : 0 ≤ M := le_trans (p2m_normInf_nonneg (s 0).x) (hx 0 (Nat.zero_le K))
  have hcomp : 0 ≤ complementarity (s k) :=
    p2m_complementarity_nonneg (s k) (by rcases hstep k hkprev with ⟨hp, _, _⟩; exact hp)
  have hcoef : 1 - (1 - δ) * stepLength r (s k) (d k) ≤ 1 - t * (1 - δ) := by
    have hfactor : 0 ≤ (1 - δ) * (stepLength r (s k) (d k) - t) :=
      mul_nonneg (le_of_lt (sub_pos.mpr hδ1)) (sub_nonneg.mpr htheta)
    nlinarith
  have hcontract := mul_le_mul_of_nonneg_right hcoef hcomp
  have hpd := p2m_primal_decay A b c δ r t hδ0 hδ1 hr0 hr1 s d K hstep hθ k hkprev
  have hdd := p2m_dual_decay A b c δ r t hδ0 hδ1 hr0 hr1 s d K hstep hθ k hkprev
  have hsum : M * norm1 (primalInfeas A b (s k)) + M * norm1 (dualInfeas A c (s k)) ≤
      M * (1 - t) ^ k *
        (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))) := by
    calc
      _ = M * (norm1 (primalInfeas A b (s k)) + norm1 (dualInfeas A c (s k))) := by ring
      _ ≤ M * ((1 - t) ^ k * norm1 (primalInfeas A b (s 0)) +
          (1 - t) ^ k * norm1 (dualInfeas A c (s 0))) :=
        mul_le_mul_of_nonneg_left (add_le_add hpd hdd) hM
      _ = _ := by ring
  calc
    complementarity (s (k + 1)) ≤
        (1 - (1 - δ) * stepLength r (s k) (d k)) * complementarity (s k)
          + (M * norm1 (primalInfeas A b (s k)) + M * norm1 (dualInfeas A c (s k))) := by
      simpa [add_assoc] using hone k hkprev
    _ ≤ (1 - t * (1 - δ)) * complementarity (s k)
          + M * (1 - t) ^ k *
            (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))) :=
      add_le_add hcontract hsum
