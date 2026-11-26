-- Prove2me | solution 1 for section5_top_eigenpair_exists
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:11.949805+00:00
-- url     : https://prove2.me/submissions/3c029c07-50b4-4cd9-80ab-2cf031949d4d

import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) :
    ∃ (v : E) (lam : ℝ), ‖v‖=1 ∧ L v=(lam:ℂ) • v ∧
      ∀ x : E, ‖x‖=1 → (inner ℂ x (L x)).re ≤ lam := by
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
  refine ⟨v,L.rayleighQuotient v,hv,heig,?_⟩
  intro y hy
  have hh := hmax (by simpa using hy : y ∈ Metric.sphere (0:E) 1)
  change RCLike.re (inner ℂ (L y) y) ≤ RCLike.re (inner ℂ (L v) v) at hh
  rw [inner_re_symm (𝕜:=ℂ) (L y) y] at hh
  have hre : RCLike.re (inner ℂ y (L y))=(inner ℂ y (L y)).re :=
    congrFun RCLike.re_eq_complex_re _
  rw [hre] at hh
  simpa only [rayleighQuotient,reApplyInnerSelf_apply,hv,one_pow,div_one] using hh
