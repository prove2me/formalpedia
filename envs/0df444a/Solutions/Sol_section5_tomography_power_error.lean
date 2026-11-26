-- Prove2me | solution 1 for section5_tomography_power_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:10:23.29458+00:00
-- url     : https://prove2.me/submissions/28a2a4c5-f875-4acc-98a2-cdbf4dbf3b0c

import Mathlib
import Theorems.Thm_section5_tomography_deflated_norm
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Quantitative deflation of a nearly pure spectral estimate. -/







theorem section5_orthogonal_positive_power {A : Type*} [Ring A]
    (X Y : A) (hXY : X*Y=0) (hYX : Y*X=0) (k : ℕ) :
    (X+Y)^(k+1)=X^(k+1)+Y^(k+1) := by
  have hX (t : ℕ) : X^(t+1)*Y=0 := by
    induction t with
    | zero => simpa using hXY
    | succ t ih => rw [pow_succ',mul_assoc,ih,mul_zero]
  have hY (t : ℕ) : Y^(t+1)*X=0 := by
    induction t with
    | zero => simpa using hYX
    | succ t ih => rw [pow_succ',mul_assoc,ih,mul_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,ih,add_mul,mul_add,mul_add,hX k,hY k,add_zero,zero_add,
      ← pow_succ,← pow_succ]

theorem section5_eigenprojection_annihilation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (lam : ℝ) (heigen : L v=(lam:ℂ) • v) :
    let P := rankOne ℂ v v
    let T := L-(lam:ℂ) • P
    ((lam:ℂ) • P)*T=0 ∧ T*((lam:ℂ) • P)=0 := by
  let P := rankOne ℂ v v
  have hPP : P*P=P := (isIdempotentElem_rankOne_self hv)
  have hLP : L*P=(lam:ℂ) • P := by
    ext x
    change L ((rankOne ℂ v v) x)=(lam:ℂ) • (rankOne ℂ v v) x
    simp only [rankOne_apply,map_smul,heigen,smul_smul]
    congr 1
    ring
  have hPL : P*L=(lam:ℂ) • P := by
    ext x
    have hh := hL.isSymmetric v x
    change inner ℂ (L v) x=inner ℂ v (L x) at hh
    rw [heigen,inner_smul_left] at hh
    simp only [Complex.conj_ofReal] at hh
    change (inner ℂ v (L x)) • v=(lam:ℂ) • (inner ℂ v x • v)
    rw [← hh,smul_smul]
  change ((lam:ℂ) • P)*(L-(lam:ℂ) • P)=0 ∧ (L-(lam:ℂ) • P)*((lam:ℂ) • P)=0
  constructor
  · rw [mul_sub,smul_mul_assoc,hPL,mul_smul_comm,smul_mul_assoc,hPP]
    simp [smul_smul]
  · rw [sub_mul,mul_smul_comm,hLP,smul_mul_assoc,mul_smul_comm,hPP]
    simp [smul_smul]

theorem section5_eigenprojection_power {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (L : E →L[ℂ] E) (hL : IsSelfAdjoint L)
    (v : E) (hv : ‖v‖=1) (lam : ℝ) (heigen : L v=(lam:ℂ) • v) (k : ℕ) :
    L^(k+1)-((lam^(k+1):ℝ):ℂ) • rankOne ℂ v v=
      (L-(lam:ℂ) • rankOne ℂ v v)^(k+1) := by
  let P := rankOne ℂ v v
  let T := L-(lam:ℂ) • P
  have hPP : P*P=P := isIdempotentElem_rankOne_self hv
  have hpow (t : ℕ) : ((lam:ℂ) • P)^(t+1)=((lam^(t+1):ℝ):ℂ) • P := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ,ih,smul_mul_assoc,mul_smul_comm,hPP,smul_smul]
      simp only [pow_succ,Complex.ofReal_mul]
  have hann := section5_eigenprojection_annihilation L hL v hv lam heigen
  change ((lam:ℂ) • P)*T=0 ∧ T*((lam:ℂ) • P)=0 at hann
  have hh := section5_orthogonal_positive_power ((lam:ℂ) • P) T hann.1 hann.2 k
  have hsum : (lam:ℂ) • P+T=L := by dsimp only [T]; abel
  rw [hsum,hpow] at hh
  change L^(k+1)-((lam^(k+1):ℝ):ℂ) • P=T^(k+1)
  rw [hh,add_sub_cancel_left]





end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (hlam : 1/2 ≤ lam) (hlow : 1-η ≤ lam)
    (herror : ‖L-rankOne ℂ w w‖ ≤ η) (heigen : L v=(lam:ℂ) • v) (k : ℕ) :
    ‖L^(k+1)-((lam^(k+1):ℝ):ℂ) • rankOne ℂ v v‖ ≤ (10*η)^(k+1) := by
  rw [section5_eigenprojection_power L hL v hv lam heigen k]
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _)
    (section5_tomography_deflated_norm L w v hw hv η lam hη hη' hlam hlow herror heigen) _)
