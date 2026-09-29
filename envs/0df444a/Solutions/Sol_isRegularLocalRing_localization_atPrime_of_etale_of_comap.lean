-- Prove2me | solution 1 for isRegularLocalRing_localization_atPrime_of_etale_of_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ce7e33e5-e736-5202-858a-fb0d3635e88c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open IsLocalRing Localization

namespace ChildB

private theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.EssFiniteType R S] :
    IsNoetherianRing S := by
  haveI hN : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S hN

end ChildB

theorem solution
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hreg
  haveI hlo : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)) q

  haveI : Algebra.FormallyUnramified A B := inferInstance
  haveI hIU : Algebra.IsUnramifiedAt A q := by
    unfold Algebra.IsUnramifiedAt
    infer_instance
  haveI hEFTa : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
  haveI hEFT : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := Algebra.EssFiniteType.of_comp A _ _
  haveI hNoeth : IsNoetherianRing (Localization.AtPrime q) :=
    ChildB.isNoetherianRing_of_essFiniteType (Localization.AtPrime (q.comap (algebraMap A B))) _

  have hmap : (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).map
      (algebraMap _ (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal

  have h1 : (maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).spanFinrank := by
    rw [← hmap]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  haveI : Module.Flat A B := inferInstance
  haveI hflat : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := inferInstance

  haveI hlom2 : (maximalIdeal (Localization.AtPrime q)).LiesOver
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))) := by
    constructor
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_iff_not.mpr
      ⟨fun h => IsLocalHom.map_nonunit x h, fun h => h.map (algebraMap _ _)⟩ |>.symm

  have h2 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := Localization.AtPrime (q.comap (algebraMap A B))) (S := Localization.AtPrime q)
    (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B))))
    (maximalIdeal (Localization.AtPrime q))

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h1
    _ = ringKrullDim (Localization.AtPrime (q.comap (algebraMap A B))) :=
        hreg.spanFinrank_maximalIdeal
    _ = ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ((maximalIdeal (Localization.AtPrime q)).height : WithBot ℕ∞) := by
        rw [h2]
        exact_mod_cast le_self_add
    _ = ringKrullDim (Localization.AtPrime q) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end

end S_isRegularLocalRing_localization_atPrime_of_etale_of_comap
end P2MW
export P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap (solution)
