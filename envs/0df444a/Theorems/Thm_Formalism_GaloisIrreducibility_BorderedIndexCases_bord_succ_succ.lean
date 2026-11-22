-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:02.512082+00:00
-- url     : https://prove2.me/theorems/5e971309-988d-4174-8bfb-725d6b529df6
-- title:
--   Bordered Index Cases: bord succ succ
-- statement:
--   The Bordered Index Cases construction uses the bord succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L23-L25

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by sorry
