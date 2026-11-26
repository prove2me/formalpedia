-- Prove2me | solution 1 for section5_tomography_rayleigh_lower
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:11.179871+00:00
-- url     : https://prove2.me/submissions/ce77d559-9c11-4969-8582-f445396bdb77

import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w : E) (hw : ‖w‖=1)
    (η lam : ℝ) (herror : ‖L-rankOne ℂ w w‖ ≤ η)
    (hmax : ∀ x : E, ‖x‖=1 → (inner ℂ x (L x)).re ≤ lam) :
    1-η ≤ lam := by
  have he := (L-rankOne ℂ w w).le_opNorm w
  have hbound : ‖(L-rankOne ℂ w w) w‖ ≤ η := by
    calc
      _ ≤ ‖L-rankOne ℂ w w‖*‖w‖ := he
      _ ≤ η := by simpa only [hw,mul_one] using herror
  have hi : ‖inner ℂ w ((L-rankOne ℂ w w) w)‖ ≤ η := by
    exact (norm_inner_le_norm w _).trans (by simpa only [hw,one_mul] using hbound)
  have hself : inner ℂ w w=(1:ℂ) := by rw [inner_self_eq_norm_sq_to_K,hw]; norm_num
  have hinner : inner ℂ w ((L-rankOne ℂ w w) w)=inner ℂ w (L w)-1 := by
    simp only [sub_apply,rankOne_apply,hself,one_smul,inner_sub_right]
  rw [hinner] at hi
  have hre := (abs_le.mp (Complex.abs_re_le_norm (inner ℂ w (L w)-1))).1
  simp only [Complex.sub_re,Complex.one_re] at hre
  linarith [hmax w hw]
