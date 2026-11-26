-- Prove2me | solution 1 for section5_spectral_estimator_exists
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:10:43.612956+00:00
-- url     : https://prove2.me/submissions/68e94920-3557-4128-966d-8e059b489fa1

import Mathlib
import Theorems.Thm_section5_tomography_spectral_recovery
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) :
    ∃ v : E, ‖v‖=1 ∧ ∀ w : E, ‖w‖=1 → ∀ η : ℝ, 0 ≤ η → η < 1/4 →
      ‖L-rankOne ℂ w w‖ ≤ η → ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖ ≤ 4*η := by
  haveI := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨x,hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have hunit : ‖NormedSpace.normalize x‖=1 := NormedSpace.norm_normalize hx
  have hnonempty : (Metric.sphere (0:E) 1).Nonempty := by
    refine ⟨NormedSpace.normalize x,?_⟩
    simpa using hunit
  obtain ⟨v,hvmem,hmax⟩ := (isCompact_sphere (0:E) 1).exists_isMaxOn hnonempty
    L.reApplyInnerSelf_continuous.continuousOn
  have hv : ‖v‖=1 := by simpa using hvmem
  have hlocal : IsLocalExtrOn L.reApplyInnerSelf (Metric.sphere (0:E) ‖v‖) v := by
    rw [hv]
    exact Or.inr hmax.localize
  have heig : L v=(L.rayleighQuotient v:ℂ) • v := hL.eq_smul_self_of_isLocalExtrOn hlocal
  have htop : ∀ y : E, ‖y‖=1 → (inner ℂ y (L y)).re ≤ L.rayleighQuotient v := by
    intro y hy
    have hh := hmax (by simpa using hy : y ∈ Metric.sphere (0:E) 1)
    change RCLike.re (inner ℂ (L y) y) ≤ RCLike.re (inner ℂ (L v) v) at hh
    rw [inner_re_symm (𝕜:=ℂ) (L y) y] at hh
    have hre : RCLike.re (inner ℂ y (L y))=(inner ℂ y (L y)).re :=
      congrFun RCLike.re_eq_complex_re _
    rw [hre] at hh
    simpa only [rayleighQuotient,reApplyInnerSelf_apply,hv,one_pow,div_one] using hh
  exact ⟨v,hv,fun w hw η hη hη' he =>
    section5_tomography_spectral_recovery L w v hw hv η (L.rayleighQuotient v) hη hη' he heig htop⟩
