-- Prove2me | solution 1 for groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/cdc20515-f647-56d5-b3da-9f4475428449

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth

set_option autoImplicit false

open CategoryTheory

local instance P2mKcShaSLevel.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance P2mKcShaSLevel.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance P2mKcShaSLevel.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace P2mKcShaSLevel

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open IntermediateField

theorem exists_finiteDimensional_fixingSubgroup_le_ker {k : Type} [CommRing k] (M : Rep k Γ) [Module.Finite k M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ M.ρ.ker := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := k) (M := M)
  choose Fi hFi hfix using fun m : ↥t => hsm (m : M)
  haveI := hFi
  refine ⟨⨆ m : ↥t, Fi m, inferInstance, fun s hs => ?_⟩
  rw [MonoidHom.mem_ker]
  have hgen : ∀ m ∈ (t : Set M), M.ρ s m = m := fun m hm =>
    hfix ⟨m, hm⟩ s (fixingSubgroup_antitone (le_iSup (fun m : ↥t => Fi m) ⟨m, hm⟩) hs)
  refine LinearMap.ext fun m => ?_
  have hm : m ∈ Submodule.span k (t : Set M) := by rw [ht]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]; rfl
  | smul c x _ hx => rw [map_smul, hx]; rfl

end P2mKcShaSLevel

open P2mKcShaSLevel IntermediateField in
theorem solution (S : Finset Nat.Primes)
    {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [Module.Finite k M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s = 1 := by
  obtain ⟨F₀, hF₀, hle₀⟩ := exists_finiteDimensional_fixingSubgroup_le_ker M hsm
  haveI := hF₀

  have hopen : IsOpen (M.ρ.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hle₀ (IntermediateField.fixingSubgroup_isOpen F₀)
  let H : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨M.ρ.ker, M.ρ.ker.isClosed_of_isOpen hopen⟩
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField M.ρ.ker
  have hFH : F.fixingSubgroup = M.ρ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have hFle : F ≤ F₀ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup F₀]
    exact IntermediateField.fixedField_le hle₀
  refine ⟨F, ⟨?_, fun q hq A hA g hg => ?_⟩, fun s hs => ?_⟩
  · exact FiniteDimensional.of_injective (IntermediateField.inclusion hFle).toLinearMap
      (IntermediateField.inclusion_injective hFle)
  · rw [hFH, MonoidHom.mem_ker]
    exact hMur q hq A hA g hg
  · rw [hFH, MonoidHom.mem_ker] at hs
    exact hs

end S_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
end P2MW
export P2MW.S_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth (solution)
