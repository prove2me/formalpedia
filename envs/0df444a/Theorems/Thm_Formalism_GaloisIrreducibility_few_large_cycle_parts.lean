-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_few_large_cycle_parts
-- name    : Formalism.GaloisIrreducibility.few_large_cycle_parts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:04.571799+00:00
-- url     : https://prove2.me/theorems/94c8a842-7bcf-4836-b54a-e2096c8da91a
-- title:
--   Galois Irreducibility: few large cycle parts
-- statement:
--   The Galois Irreducibility construction uses the few large cycle parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/FewLargeParts.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/FewLargeParts.lean#L24-L32

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset

theorem Formalism.GaloisIrreducibility.few_large_cycle_parts : FewLargeParts := by sorry
