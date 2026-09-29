-- Prove2me | solution 1 for groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c04dc470-eb9c-5e2a-ad94-6e2f9f062507

import Mathlib
import Theorems.Thm_Rep_exists_hom_coind_res_comp_eq_index_smul
import Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul

set_option autoImplicit false
open CategoryTheory

theorem solution {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (M : Rep ℤ G) (n : ℕ) :
    ∃ cor : groupCohomology (Rep.res H.subtype M) n →+ groupCohomology M n,
      ∀ x : groupCohomology M n,
        cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) n).hom x) = H.index • x := by
  obtain ⟨ι, τ, hι, -, -, hιτ⟩ := Rep.exists_hom_coind_res_comp_eq_index_smul H M

  let N : Rep ℤ H := Rep.res H.subtype M
  let Q : Rep ℤ G := Rep.coind H.subtype N

  let ev : Rep.res H.subtype Q ⟶ N := (Rep.resCoindHomEquiv H.subtype Q N).symm (𝟙 Q)
  have hev : ∀ f : Rep.res H.subtype Q, ev.hom f = (f : G → M) 1 := fun f => rfl
  have hsh := groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one N n ev hev

  have hres : groupCohomology.map (MonoidHom.id G) ι n ≫ (groupCohomology.coindIso N n).hom =
      groupCohomology.map H.subtype (𝟙 N) n := by
    rw [hsh, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
    change groupCohomology.map H.subtype ((Rep.resFunctor H.subtype).map ι ≫
      ((Rep.resFunctor (MonoidHom.id H)).map (𝟙 (Rep.res H.subtype Q)) ≫ ev)) n = _
    congr 1
    refine Rep.hom_ext (DFunLike.ext _ _ fun m => ?_)
    change ((ι.hom m : Q) : G → M) 1 = m
    rw [hι, map_one]
    rfl

  let cor : groupCohomology N n ⟶ groupCohomology M n :=
    (groupCohomology.coindIso N n).inv ≫ groupCohomology.map (MonoidHom.id G) τ n
  refine ⟨cor.hom.toAddMonoidHom, fun x => ?_⟩

  have h1 : cor.hom.toAddMonoidHom ((groupCohomology.map H.subtype (𝟙 N) n).hom x) =
      (groupCohomology.map (MonoidHom.id G) (ι ≫ τ) n).hom x := by
    change ((groupCohomology.map H.subtype (𝟙 N) n ≫ (groupCohomology.coindIso N n).inv) ≫
      groupCohomology.map (MonoidHom.id G) τ n).hom x = _
    rw [← hres, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← groupCohomology.map_id_comp]
  rw [h1]

  induction x using groupCohomology_induction_on with
  | h c =>
    rw [groupCohomology.π_map_apply, ← map_nsmul]
    congr 1
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles M n)).1 inferInstance
    rw [map_nsmul]
    change ((groupCohomology.cocyclesMap (MonoidHom.id G) (ι ≫ τ) n ≫ groupCohomology.iCocycles M n).hom c) = _
    rw [HomologicalComplex.cyclesMap_i]
    refine groupCohomology.inhomogeneousCochains.ext fun g => ?_
    change τ.hom (ι.hom (((groupCohomology.iCocycles M n).hom c) g)) = (H.index • (groupCohomology.iCocycles M n).hom c) g
    rw [hιτ, Nat.cast_smul_eq_nsmul]
    rfl

end S_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
end P2MW
export P2MW.S_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul (solution)
