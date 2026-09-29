-- Prove2me | solution 1 for groupCohomology.eq_continuousH1S_of_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/717fa29d-c6f2-5c20-ad4d-b90b7eb3d4e9

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_eq_continuousH1S_of_forall_mem_iff

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 1600000
open scoped Pointwise

theorem solution
    {k : Type} [CommRing k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (adm : Submodule k (H1 M))
    (hadm : ∀ x : H1 M, x ∈ adm ↔
      ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
        H1π M c = x) :
    adm = continuousH1S S M := by
  classical

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  apply le_antisymm

  · intro x hx
    obtain ⟨c, hlc, hur, hcx⟩ := (hadm x).1 hx
    rw [mem_continuousH1S_iff]
    refine ⟨c, ?_, hcx⟩
    have hc1 : c 1 = 0 := cocycles₁_map_one c
    have hcmul : ∀ g h, c (g * h) = M.ρ g (c h) + c g := (mem_cocycles₁_iff (⇑c)).1 c.2

    let Z : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
      { carrier := {g | c g = 0}
        one_mem' := hc1
        mul_mem' := fun {g h} hg hh => by
          show c (g * h) = 0
          rw [hcmul, (hh : c h = 0), map_zero, zero_add, (hg : c g = 0)]
        inv_mem' := fun {g} hg => by
          show c g⁻¹ = 0
          have h1 : M.ρ g (c g⁻¹) = 0 := by
            have := hcmul g g⁻¹
            rw [mul_inv_cancel, hc1, (hg : c g = 0), add_zero] at this
            exact this.symm
          have h2 := congrArg (M.ρ g⁻¹) h1
          rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h2 }
    have hZopen : IsOpen (Z : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := hlc.isOpen_fiber 0
    have hZclosed : IsClosed (Z : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := Z.isClosed_of_isOpen hZopen

    let F' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField Z
    have hFZ : F'.fixingSubgroup = Z := InfiniteGalois.fixingSubgroup_fixedField ⟨Z, hZclosed⟩
    have hFfd : FiniteDimensional ℚ F' := by
      rw [← InfiniteGalois.isOpen_iff_finite]
      show IsOpen (F'.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      rw [hFZ]
      exact hZopen
    refine ⟨F', ⟨hFfd, fun q hq A hA g hg => ?_⟩, fun g s hs => ?_⟩
    ·
      rw [hFZ]
      obtain ⟨m, hm⟩ := hur q hq A hA
      show c g = 0
      rw [hm g hg, hMur q hq A hA g hg, Module.End.one_apply, sub_self]
    ·
      rw [hFZ] at hs
      rw [hcmul, (hs : c s = 0), map_zero, zero_add]

  · intro x hx
    obtain ⟨c, ⟨F, hF, hcF⟩, hcx⟩ := (mem_continuousH1S_iff S M x).1 hx
    haveI := hF.1
    refine (hadm x).2 ⟨c, ?_, fun q hq A hA => ⟨0, fun g hg => ?_⟩, hcx⟩
    ·
      intro s
      rw [isOpen_iff_forall_mem_open]
      intro g hg
      refine ⟨g • (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), ?_,
        F.fixingSubgroup_isOpen.leftCoset g, ⟨1, F.fixingSubgroup.one_mem, mul_one g⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      show c (g * t) ∈ s
      rw [hcF g t ht]
      exact hg
    ·
      have hgF : g ∈ F.fixingSubgroup := hF.2 q hq A hA hg
      rw [map_zero, sub_self, ← one_mul g, hcF 1 g hgF]
      exact cocycles₁_map_one c

end S_groupCohomology_eq_continuousH1S_of_forall_mem_iff
end P2MW
export P2MW.S_groupCohomology_eq_continuousH1S_of_forall_mem_iff (solution)
