-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_alternating_group_not_solvable
-- name    : Formalism.GaloisIrreducibility.alternating_group_not_solvable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:54.463793+00:00
-- url     : https://prove2.me/theorems/b46c4a79-5c02-469c-82c8-16e0899162fc
-- title:
--   Galois Irreducibility: alternating group not solvable
-- statement:
--   The Galois Irreducibility construction uses the alternating group not solvable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/AltNotSolvable.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/AltNotSolvable.lean#L5-L12

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_AltNotSolvable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility

theorem Formalism.GaloisIrreducibility.alternating_group_not_solvable : AltNotSolvable := by sorry
