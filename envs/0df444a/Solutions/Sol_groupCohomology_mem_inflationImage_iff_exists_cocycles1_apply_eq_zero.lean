-- Prove2me | solution 1 for groupCohomology.mem_inflationImage_iff_exists_cocycles1_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/203bb211-c4ee-52a4-98cf-641d4282bc33

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (N : Subgroup G) [N.Normal] (x : H1 M) :
    x ∈ inflationImage M N ↔ ∃ c : cocycles₁ M, H1π M c = x ∧ ∀ n ∈ N, c n = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using H1_induction_on with | h z =>
    refine ⟨mapCocycles₁ (QuotientGroup.mk' N) (Rep.ofHom (M.ρ.quotientToInvariants_lift N)) z,
      ?_, ?_⟩
    · exact (show (inflation M N).hom (H1π (M.quotientToInvariants N) z)
          = H1π M (mapCocycles₁ (QuotientGroup.mk' N)
              (Rep.ofHom (M.ρ.quotientToInvariants_lift N)) z) from
        H1π_comp_map_apply _ _ _).symm
    intro n hn
    have h1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show (z ((QuotientGroup.mk' N) n)).1 = 0
    rw [h1, cocycles₁_map_one]
    rfl
  · rintro ⟨c, rfl, hc⟩
    have hexact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (H1InfRes_exact M N)
    change H1π M c ∈ LinearMap.range (ModuleCat.Hom.hom (H1InfRes M N).f)
    rw [hexact]
    have hres : ModuleCat.Hom.hom (H1InfRes M N).g (H1π M c)
        = H1π (Rep.res N.subtype M) (mapCocycles₁ N.subtype (𝟙 _) c) :=
      H1π_comp_map_apply _ _ _
    have hzero : mapCocycles₁ N.subtype (𝟙 (Rep.res N.subtype M)) c = 0 :=
      cocycles₁_ext fun n => hc n.1 n.2
    change (ModuleCat.Hom.hom (H1InfRes M N).g) (H1π M c) = 0
    refine hres.trans ?_
    rw [hzero]
    exact map_zero _

end S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero
end P2MW
export P2MW.S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero (solution)
