-- Prove2me | solution 1 for invariant_subspace_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:40:13.78045+00:00
-- url     : https://prove2.me/submissions/cc69f4a8-ed39-421b-89ca-103adc06d612

import Mathlib

set_option autoImplicit false

-- Adapted from ryanshin ACCEPTED b3e2e380-6561-4c14-b6b0-444725a4ef3b.
-- Legacy target: 73cae8f2-f0d4-4497-b8df-0aebeafed525.

-- Source module: Main.lean
namespace AlgebraicInvariantSubspace

theorem exists_invariant_submodule (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] (hinfty : ¬FiniteDimensional ℂ H)
    (T : H →L[ℂ] H) :
    ∃ S : Submodule ℂ H,
      S ≠ ⊥ ∧ S ≠ ⊤ ∧
      S ∈ Module.End.invtSubmodule (T : H →ₗ[ℂ] H) := by
  classical
  have hnontrivial : ¬Subsingleton H := by
    intro h
    letI : Subsingleton H := h
    exact hinfty inferInstance
  letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hnontrivial
  obtain ⟨z, hz⟩ := spectrum.nonempty T
  let U : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - T
  have hnotbij : ¬Function.Bijective U := by
    intro h
    exact (spectrum.mem_iff.mp hz) (ContinuousLinearMap.isUnit_iff_bijective.mpr h)
  have hcomm (x : H) : T (U x) = U (T x) := by
    simp [U, map_sub, map_smul]
  by_cases hU : U = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : H)
    refine ⟨Submodule.span ℂ {v}, ?_, ?_, ?_⟩
    · exact fun h => hv (Submodule.span_singleton_eq_bot.mp h)
    · intro htop
      apply hinfty
      apply FiniteDimensional.of_surjective (Submodule.span ℂ {v}).subtype
      intro x
      exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩
    · rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
      intro x hx
      have hscalar : T x = z • x := by
        have heq := DFunLike.congr_fun hU x
        change z • x - T x = 0 at heq
        exact (sub_eq_zero.mp heq).symm
      change T x ∈ Submodule.span ℂ {v}
      rw [hscalar]
      exact Submodule.smul_mem _ z hx
  · have hUlin : (U : H →ₗ[ℂ] H) ≠ 0 := by
      intro h
      apply hU
      ext x
      exact DFunLike.congr_fun h x
    by_cases hinj : Function.Injective U
    -- The range is an algebraic submodule; it need not be closed.
    · refine ⟨LinearMap.range (U : H →ₗ[ℂ] H), ?_, ?_, ?_⟩
      · exact fun h => hUlin (LinearMap.range_eq_bot.mp h)
      · exact fun h => hnotbij ⟨hinj, LinearMap.range_eq_top.mp h⟩
      · rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
        rintro x ⟨y, rfl⟩
        exact ⟨T y, (hcomm y).symm⟩
    · refine ⟨LinearMap.ker (U : H →ₗ[ℂ] H), ?_, ?_, ?_⟩
      · exact fun h => hinj (LinearMap.ker_eq_bot.mp h)
      · exact fun h => hUlin (LinearMap.ker_eq_top.mp h)
      · rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
        intro x hx
        change U x = 0 at hx
        change U (T x) = 0
        rw [← hcomm, hx, map_zero]

end AlgebraicInvariantSubspace

theorem solution (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinfty : ¬FiniteDimensional ℂ H)
    (T : H →L[ℂ] H) (hT : T ≠ 0) :
    ∃ S : Submodule ℂ H,
      S ≠ ⊥ ∧ S ≠ ⊤ ∧
      S ∈ Module.End.invtSubmodule (T : H →ₗ[ℂ] H) := by
  exact AlgebraicInvariantSubspace.exists_invariant_submodule H hinfty T

#check @solution
#print axioms solution

