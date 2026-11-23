-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_restriction_of_blocks_and_jordan
-- name    : Formalism.CyclotomicNorms.restriction_of_blocks_and_jordan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:14.210298+00:00
-- url     : https://prove2.me/theorems/321a8ec7-07df-488c-8528-4db5af1d2a36
-- title:
--   Cyclotomic Norms: restriction of blocks and jordan
-- statement:
--   The Cyclotomic Norms construction uses the restriction of blocks and jordan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L90-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L90-L433

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms

theorem Formalism.CyclotomicNorms.restriction_of_blocks_and_jordan (hB : BlocksCycle) (hJ : JordanTransitive) : Restriction := by sorry
