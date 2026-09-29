-- Prove2me | solution 1 for groupCohomology.unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7845e41b-243e-5392-b475-daa7b5d9c0a5

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2

set_option autoImplicit false
open CategoryTheory groupCohomology
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open groupCohomology IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (E : IntermediateField K (PadicAlgCl q))
    (N : ℕ)
    [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (j : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) →* ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (hj : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})),
      (x : PadicAlgCl q) = (y : PadicAlgCl q) → ((j σ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ((σ y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (ψ : Rep.res j (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ⟶ Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
    (hψ : ∀ u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ,
      (((Additive.toMul (ψ.hom (Additive.ofMul u)) : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q)
        = ((u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (f : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) × ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) → Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) :
    (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1, (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2)
        - unitsInflate₂ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (fun p => ψ.hom (f (j p.1, j p.2))) g)
      ∈ levelCoboundaries₂ (r.comp (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom)) (Rep.ofAlgebraAutOnUnits E (PadicAlgCl q)) := by
  have hιapp : ∀ (σ : PadicAlgCl q ≃ₐ[E] PadicAlgCl q) (z : PadicAlgCl q),
      (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) σ z = σ z :=
    fun _ _ => rfl

  have hsub : ∀ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), ∃ y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), (x : PadicAlgCl q) = (y : PadicAlgCl q) := by
    intro x
    have hle : IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      exact IntermediateField.subset_adjoin E _ hz
    exact ⟨⟨(x : PadicAlgCl q), hle x.2⟩, rfl⟩

  have hjres : ∀ σ : PadicAlgCl q ≃ₐ[E] PadicAlgCl q,
      j (AlgEquiv.restrictNormalHom (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) σ)
        = AlgEquiv.restrictNormalHom (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
            ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) σ) := by
    intro σ
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨y, hxy⟩ := hsub x
    apply Subtype.ext
    have h1 := hj (AlgEquiv.restrictNormalHom (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) σ) x y hxy
    rw [h1]
    have h2 : (((AlgEquiv.restrictNormalHom (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) σ) y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = σ (y : PadicAlgCl q) :=
      AlgEquiv.restrictNormal_commutes σ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) y
    have h3 : (((AlgEquiv.restrictNormalHom (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
        ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) σ)) x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q)
        = ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) σ) (x : PadicAlgCl q) :=
      AlgEquiv.restrictNormal_commutes _ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) x
    rw [h2, h3, hιapp, hxy]

  have hzero : (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1, (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2)
        - unitsInflate₂ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (fun p => ψ.hom (f (j p.1, j p.2))) g) = 0 := by
    funext g
    obtain ⟨σ, τ⟩ := g
    rw [Pi.zero_apply, sub_eq_zero]
    apply Additive.toMul.injective
    apply Units.ext
    rw [coe_toMul_unitsInflate₂, coe_toMul_unitsInflate₂]
    simp only
    rw [hjres, hjres]
    symm
    have := hψ (Additive.toMul (f (AlgEquiv.restrictNormalHom (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) σ),
      AlgEquiv.restrictNormalHom (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) τ))))
    simp only [ofMul_toMul] at this
    exact this
  rw [hzero]
  exact Submodule.zero_mem _

end S_groupCohomology_unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2 (solution)
