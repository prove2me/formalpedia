-- Prove2me | solution 1 for section5_power_column_estimator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:51.568272+00:00
-- url     : https://prove2.me/submissions/558fe7ac-5890-44fa-b96e-49b4eea2448f

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_max_column_recovery
import Theorems.Thm_section5_tomography_eigenvector_recovery
import Theorems.Thm_section5_tomography_power_error
import Theorems.Thm_section5_tomography_rayleigh_lower
import Theorems.Thm_section5_top_eigenpair_exists
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1))
    (j : Fin n) (hmax : ∀ i, ‖(L^(k+1)) (section5_coordinate_ket i)‖ ≤
      ‖(L^(k+1)) (section5_coordinate_ket j)‖)
    (w : EuclideanSpace ℂ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖L-rankOne ℂ w w‖ ≤ ε/1000) :
    (L^(k+1)) (section5_coordinate_ket j) ≠ 0 ∧
      ∃ ζ : ℂ, ‖ζ‖=1 ∧
        ‖NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-ζ • w‖ ≤ ε/24 := by
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨v,lam,hv,heigen,hmaxeig⟩ := section5_top_eigenpair_exists L hL
  let η := ε/1000
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hη' : η < 1/4 := by dsimp only [η]; linarith
  have hlow : 1-η ≤ lam := section5_tomography_rayleigh_lower L w hw η lam herror hmaxeig
  have hlam : 1/2 ≤ lam := by dsimp only [η] at hlow; linarith
  have hlam0 : 0 < lam := by linarith
  have hratio : 2*(10*η) ≤ lam := by dsimp only [η] at *; linarith
  let α := lam^(k+1)
  let ρ := (10*η)^(k+1)
  have hα : 0 < α := pow_pos hlam0 _
  have hρ : 0 ≤ ρ := pow_nonneg (by positivity) _
  have hpow : (2:ℝ)^(k+1)*ρ ≤ α := by
    dsimp only [α,ρ]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hratio _
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hprec' : 400*(n:ℝ) ≤ (2:ℝ)^(k+1)*ε := (div_le_iff₀ hε).mp hprec
  have htwo : 4*(n:ℝ) ≤ (2:ℝ)^(k+1) := by
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (k+1)]
  have hsmall : 4*(n:ℝ)*ρ ≤ α :=
    (mul_le_mul_of_nonneg_right htwo hρ).trans hpow
  have hAerror : ‖L^(k+1)-(α:ℂ) • rankOne ℂ v v‖ ≤ ρ :=
    section5_tomography_power_error L hL w v hw hv η lam hη hη' hlam hlow herror heigen k
  obtain ⟨hy0,ζ,hζ,hclose⟩ := section5_max_column_recovery hn (L^(k+1)) j hmax v hv
    α ρ hα hρ hsmall hAerror
  have hdecay : 4*(n:ℝ)*ρ/α ≤ ε/100 := by
    apply (div_le_iff₀ hα).mpr
    have hh := mul_le_mul_of_nonneg_right hprec' hρ
    have hh' := mul_le_mul_of_nonneg_right hpow hε.le
    nlinarith
  obtain ⟨θ,hθ,hvclose⟩ := section5_tomography_eigenvector_recovery L w v hw hv η lam
    hη hη' hlam herror heigen
  refine ⟨hy0,ζ*θ,by simp [norm_mul,hζ,hθ],?_⟩
  have htri := norm_add_le
    (NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-ζ • v)
    (ζ • (v-θ • w))
  have hid : (NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-ζ • v)+
      ζ • (v-θ • w)=NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-(ζ*θ) • w := by
    rw [smul_sub,smul_smul]
    abel
  rw [hid,norm_smul,hζ,one_mul] at htri
  dsimp only [η] at hvclose
  linarith
