-- Prove2me | solution 1 for groupCohomology.map_inflationImage_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/21cb6ae0-3064-54f9-b7d1-03ed2bd60157

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_map_inflationImage_le

open CategoryTheory Module groupCohomology

universe u

theorem solution {k : Type u} [CommRing k] {G : Type u} [Group G] {Δ : Type u} [Group Δ] (f : Δ →* G) {M : Rep k G} {N : Rep k Δ}
    (φ : Rep.res f M ⟶ N) (T : Subgroup G) [T.Normal] (S : Subgroup Δ) [S.Normal]
    (hST : S ≤ T.comap f) :
    (inflationImage M T).map (groupCohomology.map f φ 1).hom ≤ inflationImage N S := by
  rw [Submodule.map_le_iff_le_comap]
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_comap]

  induction y using H1_induction_on with | h z =>

  set π : Δ ⧸ S →* G ⧸ T := QuotientGroup.map S T f hST with hπdef
  have hπ : ∀ δ : Δ, π (δ : Δ ⧸ S) = ((f δ : G) : G ⧸ T) := fun δ => rfl

  have hinv : ∀ q : G ⧸ T,
      φ.hom (z q).1 ∈ Representation.invariants (N.ρ.comp S.subtype) := by
    intro q
    rw [Representation.mem_invariants]
    intro s
    have h1 : M.ρ (f s.1) (z q).1 = (z q).1 := (z q).2 (⟨f s.1, hST s.2⟩ : T)
    have h2 := Rep.hom_comm_apply φ s.1 (z q).1
    show N.ρ s.1 (φ.hom (z q).1) = φ.hom (z q).1
    rw [← h2]
    exact congrArg φ.hom h1

  set w : (Δ ⧸ S) → (N.quotientToInvariants S) :=
    fun q => ⟨φ.hom (z (π q)).1, hinv (π q)⟩ with hwdef
  have hwcoc : w ∈ cocycles₁ (N.quotientToInvariants S) := by
    rw [mem_cocycles₁_iff]
    intro q₁ q₂
    refine QuotientGroup.induction_on q₁ fun δ₁ => ?_
    refine QuotientGroup.induction_on q₂ fun δ₂ => ?_

    refine Subtype.ext ?_
    show φ.hom (z (π ((δ₁ : Δ ⧸ S) * (δ₂ : Δ ⧸ S)))).1
      = N.ρ δ₁ (φ.hom (z (π (δ₂ : Δ ⧸ S))).1) + φ.hom (z (π (δ₁ : Δ ⧸ S))).1
    have hπmul : π ((δ₁ : Δ ⧸ S) * (δ₂ : Δ ⧸ S))
        = ((f δ₁ : G) : G ⧸ T) * ((f δ₂ : G) : G ⧸ T) := by
      rw [map_mul, hπ δ₁, hπ δ₂]

    have hz := (mem_cocycles₁_iff (A := M.quotientToInvariants T) ⇑z).1 z.2
      ((f δ₁ : G) : G ⧸ T) ((f δ₂ : G) : G ⧸ T)
    have hz1 : (z (((f δ₁ : G) : G ⧸ T) * ((f δ₂ : G) : G ⧸ T))).1
        = M.ρ (f δ₁) (z ((f δ₂ : G) : G ⧸ T)).1 + (z ((f δ₁ : G) : G ⧸ T)).1 :=
      congrArg Subtype.val hz
    rw [hπmul, hπ δ₁, hπ δ₂, hz1, map_add]
    congr 1
    exact Rep.hom_comm_apply φ δ₁ (z ((f δ₂ : G) : G ⧸ T)).1

  refine ⟨H1π _ ⟨w, hwcoc⟩, ?_⟩

  rw [show (inflation N S).hom (H1π (N.quotientToInvariants S) ⟨w, hwcoc⟩)
      = H1π N (mapCocycles₁ (QuotientGroup.mk' S)
          (Rep.ofHom (N.ρ.quotientToInvariants_lift S)) ⟨w, hwcoc⟩) from
    H1π_comp_map_apply _ _ _]
  rw [show (inflation M T).hom (H1π (M.quotientToInvariants T) z)
      = H1π M (mapCocycles₁ (QuotientGroup.mk' T)
          (Rep.ofHom (M.ρ.quotientToInvariants_lift T)) z) from
    H1π_comp_map_apply _ _ _]
  rw [show (groupCohomology.map f φ 1).hom (H1π M (mapCocycles₁ (QuotientGroup.mk' T)
          (Rep.ofHom (M.ρ.quotientToInvariants_lift T)) z))
      = H1π N (mapCocycles₁ f φ (mapCocycles₁ (QuotientGroup.mk' T)
          (Rep.ofHom (M.ρ.quotientToInvariants_lift T)) z)) from
    H1π_comp_map_apply _ _ _]
  rw [show (mapCocycles₁ (QuotientGroup.mk' S)
      (Rep.ofHom (N.ρ.quotientToInvariants_lift S)) ⟨w, hwcoc⟩ : cocycles₁ N)
    = mapCocycles₁ f φ (mapCocycles₁ (QuotientGroup.mk' T)
        (Rep.ofHom (M.ρ.quotientToInvariants_lift T)) z) from
    cocycles₁_ext fun δ => rfl]

end S_groupCohomology_map_inflationImage_le
end P2MW
export P2MW.S_groupCohomology_map_inflationImage_le (solution)
