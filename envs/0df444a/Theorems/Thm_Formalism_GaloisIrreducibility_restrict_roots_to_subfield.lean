-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_restrict_roots_to_subfield
-- name    : Formalism.GaloisIrreducibility.restrict_roots_to_subfield
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:25.776465+00:00
-- url     : https://prove2.me/theorems/aeb8e279-623e-4bf9-a6af-b07fa3adb1c4
-- title:
--   Galois Irreducibility: restrict roots to subfield
-- statement:
--   The Galois Irreducibility construction uses the restrict roots to subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L165-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L165-L193

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Module Polynomial

theorem Formalism.GaloisIrreducibility.restrict_roots_to_subfield : RestrictRoots := by sorry
