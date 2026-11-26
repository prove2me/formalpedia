-- Prove2me | solution 1 for section5_normalize_real_direction
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:52.893807+00:00
-- url     : https://prove2.me/submissions/7f471c6c-9659-4cba-9fd7-42b5323edded

import Mathlib
import Theorems.Thm_section5_normalize_perturbation
set_option autoImplicit false
theorem solution {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (r w : V) (c δ : ℝ) (hw : ‖w‖ = 1)
    (hc : 1/2 < |c|) (hδ : 0 ≤ δ) (hδ' : δ < 1/2)
    (hclose : ‖r - c • w‖ ≤ δ) :
    r ≠ 0 ∧ ‖‖r‖⁻¹ • r - (SignType.sign c : ℝ) • w‖ ≤ 4 * δ := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hc0 : c ≠ 0 := abs_pos.mp (by linarith)
  have hcw : ‖c • w‖ = |c| := by simp [norm_smul, hw]
  have hr : r ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, hcw] at hclose
    linarith
  refine ⟨hr, ?_⟩
  have hn := section5_normalize_perturbation r (c • w) hr (smul_ne_zero hc0 hw0)
  rw [NormedSpace.normalize_smul,
    NormedSpace.normalize_eq_self_of_norm_eq_one hw, hcw] at hn
  change ‖‖r‖⁻¹ • r - (SignType.sign c : ℝ) • w‖ ≤ _ at hn
  have hb : 2 * ‖r-c • w‖ / |c| ≤ 4 * δ := by
    apply (div_le_iff₀ (lt_trans (by norm_num) hc)).mpr
    nlinarith
  exact hn.trans hb
