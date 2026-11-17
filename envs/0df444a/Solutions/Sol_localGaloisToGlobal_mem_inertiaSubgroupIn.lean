-- Prove2me | solution 1 for localGaloisToGlobal_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:48.513839+00:00
-- url     : https://prove2.me/submissions/448e02df-4490-495b-95c7-59a338bb334b

import Definitions.Def_GaloisRep_CompletionBridge

set_option autoImplicit false

/-- Local inertia maps into global inertia at the valuation defined by the
chosen embedding of the algebraic closure. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) :
    localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ := by
  obtain ⟨t, ht, rfl⟩ := hτ
  let g : (padicPlace p).decompositionSubgroup ℚ :=
    ⟨localGaloisToGlobal p t, localGaloisToGlobal_mem_decompositionSubgroup p t⟩
  refine ⟨g, ?_, rfl⟩
  change MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField (padicPlace p)) g = 1
  ext y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := padicPlace p) y
  change g • IsLocalRing.residue (padicPlace p) x = IsLocalRing.residue (padicPlace p) x
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  apply ValuationSubring.coe_mem_nonunits_iff.mp
  have hreflect (a : AlgebraicClosure ℚ)
      (ha : padicEmbedding p a ∈ (padicIntegers p).nonunits) :
      a ∈ (padicPlace p).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at ha ⊢
    rcases ha with ha | ha
    · left
      exact (padicEmbedding p).injective (ha.trans (map_zero _).symm)
    · right
      intro h
      apply ha
      change padicEmbedding p (a⁻¹) ∈ padicIntegers p at h
      rwa [map_inv₀] at h
  apply hreflect
  let u : padicIntegers p := ⟨padicEmbedding p (x : AlgebraicClosure ℚ), x.property⟩
  have hres : IsLocalRing.residue (padicIntegers p) (t • u - u) = 0 := by
    rw [map_sub, IsLocalRing.ResidueField.residue_smul]
    change MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField (padicIntegers p)) t = 1 at ht
    have heq := congrArg (fun e : RingAut (IsLocalRing.ResidueField (padicIntegers p)) =>
      e (IsLocalRing.residue (padicIntegers p) u)) ht
    exact sub_eq_zero.mpr heq
  have hnu := ValuationSubring.coe_mem_nonunits_iff.mpr
    ((IsLocalRing.residue_eq_zero_iff _).mp hres)
  change padicEmbedding p (localGaloisToGlobal p t (x : AlgebraicClosure ℚ) - x) ∈
    (padicIntegers p).nonunits
  rw [map_sub, padicEmbedding_localGaloisToGlobal]
  exact hnu
