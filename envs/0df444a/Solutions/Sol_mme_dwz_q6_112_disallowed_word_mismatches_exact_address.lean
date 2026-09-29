-- Prove2me | solution 1 for mme_dwz_q6_112_disallowed_word_mismatches_exact_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:32:45.210896+00:00
-- url     : https://prove2.me/submissions/95d1efba-6f07-4c1f-b922-ca1d03a7a08c

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_q6_112_exact_profile_data
import Theorems.Thm_mme_dwz_q6_112_exact_address_allowed_histogram

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

theorem solution
    (m : ℕ)
    (address : CWQ6ExactCoupledAddress
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)))
    (labelGrade : LiftedCoarsePair.{u} 6 2 → Fin 3)
    (htranslate : ∀ p,
      p.leftGrade = mme_dwz_q6_coupled_Z_leftGrade (labelGrade p))
    (w : PowIndex (LiftedCoarsePair.{u} 6 2)
      (MME.DWZTable2Counts.component (12 : Fin 15) * m))
    (hnot : ¬ componentWordAllowed (12 : Fin 15) m w) :
    ∃ hlen : MME.DWZTable2Counts.component (12 : Fin 15) * m =
        2 * (50000000 * (20088623 * m)),
      ∃ r : Fin (MME.DWZTable2Counts.component (12 : Fin 15) * m),
        labelGrade (PowIndex.get _ w r) ≠
          address.1 2 (Fin.cast hlen r) := by
  obtain ⟨hlen', hprofile⟩ :=
    mme_dwz_q6_112_exact_address_allowed_histogram m address
  let hlen := hlen'.symm
  refine ⟨hlen, ?_⟩
  by_contra hnone
  push Not at hnone
  apply hnot
  intro a
  let e :
      Fin (MME.DWZTable2Counts.component (12 : Fin 15) * m) ≃
        Fin (2 * (50000000 * (20088623 * m))) :=
    finCongr hlen
  have hprop (r : Fin
      (MME.DWZTable2Counts.component (12 : Fin 15) * m)) :
      (PowIndex.get _ w r).leftGrade = a ↔
        mme_dwz_q6_coupled_Z_leftGrade (address.1 2 (e r)) = a := by
    rw [htranslate]
    rw [hnone r]
    rfl
  calc
    Fintype.card
        {r : Fin (MME.DWZTable2Counts.component (12 : Fin 15) * m) //
          (PowIndex.get _ w r).leftGrade = a} =
      Fintype.card
        {r : Fin (2 * (50000000 * (20088623 * m))) //
          mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = a} := by
            exact Fintype.card_congr (e.subtypeEquiv hprop)
    _ = MME.DWZTable2Counts.split (12 : Fin 15) a * m :=
      hprofile a
