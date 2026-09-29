-- Prove2me | solution 1 for mme_dwz_component_word_allowed_reindex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:16:25.782358+00:00
-- url     : https://prove2.me/submissions/c9bd3a1c-0d8e-4eb6-bcd2-745b587f4fc3

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_kron_pow_word_reindex

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm
      (Fin (MME.DWZTable2Counts.component s * m)))
    (w : MME.DWZComponentRestriction.PowIndex
      (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m)) :
    MME.DWZComponentRestriction.componentWordAllowed s m
        (MME.DWZComponentRestriction.PowIndex.reindex e w) ↔
      MME.DWZComponentRestriction.componentWordAllowed s m w := by
  constructor <;> intro h a
  · calc
      Fintype.card
          {r : Fin (MME.DWZTable2Counts.component s * m) //
            (MME.DWZComponentRestriction.PowIndex.get _ w r).leftGrade = a} =
          Fintype.card
            {r : Fin (MME.DWZTable2Counts.component s * m) //
              (MME.DWZComponentRestriction.PowIndex.get _
                (MME.DWZComponentRestriction.PowIndex.reindex e w) r).leftGrade = a} := by
        symm
        exact Fintype.card_congr
          (Equiv.subtypeEquiv e (fun _ => by
            simp only [MME.DWZComponentRestriction.PowIndex.get_reindex]))
      _ = MME.DWZTable2Counts.split s a * m := h a
  · calc
      Fintype.card
          {r : Fin (MME.DWZTable2Counts.component s * m) //
            (MME.DWZComponentRestriction.PowIndex.get _
              (MME.DWZComponentRestriction.PowIndex.reindex e w) r).leftGrade = a} =
          Fintype.card
            {r : Fin (MME.DWZTable2Counts.component s * m) //
              (MME.DWZComponentRestriction.PowIndex.get _ w r).leftGrade = a} := by
        exact Fintype.card_congr
          (Equiv.subtypeEquiv e (fun _ => by
            simp only [MME.DWZComponentRestriction.PowIndex.get_reindex]))
      _ = MME.DWZTable2Counts.split s a * m := h a
