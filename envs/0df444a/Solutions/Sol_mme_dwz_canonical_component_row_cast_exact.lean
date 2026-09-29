-- Prove2me | solution 1 for mme_dwz_canonical_component_row_cast_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:47:29.751303+00:00
-- url     : https://prove2.me/submissions/f878d1d4-8c57-4233-bfda-53eb8fdb2d41

import Definitions.Def_mme_dwz_canonical_component_row_cast_data
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {s t : Fin 15} (h : s = t) :
    PiTensorProduct.map
        (fun i ↦ (MME.DWZSourceAligned.canonicalComponentModeCast
          (K := K) h i).toLinearMap)
        (MME.DWZComponentRestriction.canonicalComponentBlock K s).t =
      (MME.DWZComponentRestriction.canonicalComponentBlock K t).t ∧
    (∀ x : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s),
      HEq
        (MME.DWZSourceAligned.canonicalComponentModeCast (K := K) h 2
          (MME.DWZComponentRestriction.canonicalComponentZBasis K s x))
        (MME.DWZComponentRestriction.canonicalComponentZBasis K t
          (MME.DWZSourceAligned.canonicalComponentZLetterCast h x))) ∧
    ∀ x : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s),
      HEq (MME.DWZSourceAligned.canonicalComponentZLetterCast h x) x := by
  subst t
  refine ⟨?_, fun _ ↦ HEq.rfl, fun _ ↦ HEq.rfl⟩
  change PiTensorProduct.map (fun _ : Fin 3 ↦ LinearMap.id)
      (MME.DWZComponentRestriction.canonicalComponentBlock K s).t = _
  rw [PiTensorProduct.map_id]
  exact LinearMap.id_apply _
