-- Prove2me | solution 1 for mme_dwz_component_word_allowed_iff_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:08:33.524779+00:00
-- url     : https://prove2.me/submissions/4e4c07ea-df77-46f8-8825-44657d2c5b8f

import Definitions.Def_mme_dwz_component_word_projection

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (s : Fin 15) (m : ℕ)
    (w : MME.DWZComponentRestriction.PowIndex
      (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m)) :
    MME.DWZComponentRestriction.componentWordAllowed s m w ↔
      ∀ a : Fin 3,
        Fintype.card
            {r : Fin (MME.DWZTable2Counts.component s * m) //
              (MME.DWZComponentRestriction.PowIndex.get _ w r).leftGrade = a} =
          MME.DWZTable2Counts.split s a * m := by
  rfl
