-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_one
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.bord_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:14.637132+00:00
-- url     : https://prove2.me/theorems/1c634ef9-617b-4195-b0e3-f0c949e8292a
-- title:
--   Bordered Index Cases: bord one
-- statement:
--   The Bordered Index Cases construction uses the bord one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L32-L35

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

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.bord_one {m : ℕ} : bord (1 : Matrix (Fin m) (Fin m) R) = 1 := by sorry
