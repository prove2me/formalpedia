-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_isUnit
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.bord_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:09.1836+00:00
-- url     : https://prove2.me/theorems/9aad1dd2-0701-4ac2-8640-f7e3cd9e9145
-- title:
--   Bordered Index Cases: bord is Unit
-- statement:
--   The Bordered Index Cases construction uses the bord is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L37-L45

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

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.bord_isUnit {m : ℕ} {M : Matrix (Fin m) (Fin m) R} (h : IsUnit M) : IsUnit (bord M) := by sorry
