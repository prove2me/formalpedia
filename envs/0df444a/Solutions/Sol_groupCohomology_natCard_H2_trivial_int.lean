-- Prove2me | solution 1 for groupCohomology.natCard_H2_trivial_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/207e808b-ec2e-55ea-adc7-703f5051ea2a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_H2_trivial_int

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

theorem solution
    {G : Type} [Group G] [Finite G] [IsCyclic G] :
    Nat.card (H2 (Rep.trivial ℤ G ℤ)) = Nat.card G := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  rw [Nat.card_congr (groupCohomologyIsoEven (Rep.trivial ℤ G ℤ) g hg 2 (by decide)).toLinearEquiv.toEquiv,
    Nat.card_congr (normHomCompSub (Rep.trivial ℤ G ℤ) g).moduleCatHomologyIso.toLinearEquiv.toEquiv]
  set S := normHomCompSub (Rep.trivial ℤ G ℤ) g with hS
  change Nat.card (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = _

  have hD : ∀ x, S.g.hom x = 0 := fun x => by
    change (Rep.trivial ℤ G ℤ).ρ g x - x = 0
    simp
  have hker : LinearMap.ker S.g.hom = ⊤ := eq_top_iff.2 fun x _ => hD x

  have hN : ∀ x : ℤ, (S.f.hom x : ℤ) = (Fintype.card G : ℤ) * x := fun x => by
    change ((Rep.trivial ℤ G ℤ).norm).hom x = _
    rw [Rep.norm_apply]
    simp [Representation.norm, Finset.card_univ]
  let e : LinearMap.ker S.g.hom ≃ₗ[ℤ] ℤ := LinearEquiv.ofTop _ hker
  have hmap : (LinearMap.range S.moduleCatToCycles).map (e : LinearMap.ker S.g.hom →ₗ[ℤ] ℤ)
      = Ideal.span {(Fintype.card G : ℤ)} := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      refine ⟨x, ?_⟩
      change x * (Fintype.card G : ℤ) = S.f.hom x
      rw [hN, mul_comm]
    · rintro ⟨a, rfl⟩
      refine ⟨S.moduleCatToCycles a, ⟨a, rfl⟩, ?_⟩
      change S.f.hom a = a * (Fintype.card G : ℤ)
      rw [hN, mul_comm]
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ e hmap).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod (Fintype.card G)).toEquiv, Nat.card_zmod,
    Nat.card_eq_fintype_card]

end S_groupCohomology_natCard_H2_trivial_int
end P2MW
export P2MW.S_groupCohomology_natCard_H2_trivial_int (solution)
