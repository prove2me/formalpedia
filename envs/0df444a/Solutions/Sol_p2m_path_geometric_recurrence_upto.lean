-- Prove2me | solution 1 for p2m_path_geometric_recurrence_upto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:51:11.723505+00:00
-- url     : https://prove2.me/submissions/4eadbaa4-fdd6-437e-9bdf-f09dd6c73c61

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
theorem solution {δ t M R : ℝ} (K : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (γ : ℕ → ℝ)
    (hrec : ∀ k, k + 1 ≤ K →
      γ (k + 1) ≤ (1 - t * (1 - δ)) * γ k + M * (1 - t) ^ k * R) :
    ∀ k ≤ K, γ k ≤ (1 - t * (1 - δ)) ^ k * (γ 0 + M * R / (δ * t)) := by
  let q := 1 - t * (1 - δ)
  let a := 1 - t
  let E := M * R / (δ * t)
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hqa : a ≤ q := by dsimp [a, q]; nlinarith [mul_pos ht0 hδ0]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_of_lt hδ1))]
  have hqa' : q - a = δ * t := by dsimp [q, a]; ring
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact div_nonneg (mul_nonneg hM hR) (le_of_lt (mul_pos hδ0 ht0))
  have hEid : E * (q - a) = M * R := by
    rw [hqa']
    dsimp [E]
    field_simp [ne_of_gt (mul_pos hδ0 ht0)]
  intro k hk
  have hinv : γ k ≤ q ^ k * γ 0 + E * (q ^ k - a ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hkprev : k ≤ K := le_trans (Nat.le_succ k) hk
        have hkstep : k + 1 ≤ K := by simpa using hk
        calc
          γ (k + 1) ≤ q * γ k + M * a ^ k * R := by
            simpa [q, a] using hrec k hkstep
          _ ≤ q * (q ^ k * γ 0 + E * (q ^ k - a ^ k)) + M * a ^ k * R :=
            add_le_add (mul_le_mul_of_nonneg_left (ih hkprev) hq0) le_rfl
          _ = q ^ (k + 1) * γ 0 + E * (q ^ (k + 1) - a ^ (k + 1)) := by
            calc
              _ = q * (q ^ k * γ 0 + E * (q ^ k - a ^ k)) + a ^ k * (M * R) := by ring
              _ = q * (q ^ k * γ 0 + E * (q ^ k - a ^ k)) + a ^ k * (E * (q - a)) := by
                rw [← hEid]
              _ = _ := by rw [pow_succ, pow_succ]; ring
  have hpow : 0 ≤ a ^ k := pow_nonneg ha0 _
  have herr : E * (q ^ k - a ^ k) ≤ E * q ^ k := by nlinarith [mul_nonneg hE0 hpow]
  calc
    γ k ≤ q ^ k * γ 0 + E * (q ^ k - a ^ k) := hinv
    _ ≤ q ^ k * γ 0 + E * q ^ k := add_le_add_right herr _
    _ = q ^ k * (γ 0 + E) := by ring
    _ = (1 - t * (1 - δ)) ^ k * (γ 0 + M * R / (δ * t)) := by simp [q, E]
end
