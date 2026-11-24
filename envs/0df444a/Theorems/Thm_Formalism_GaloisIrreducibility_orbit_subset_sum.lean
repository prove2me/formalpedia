-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_orbit_subset_sum
-- name    : Formalism.GaloisIrreducibility.orbit_subset_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:24.622234+00:00
-- url     : https://prove2.me/theorems/8880c88b-0816-43b2-9a26-d08bc163c244
-- title:
--   Galois Irreducibility: orbit subset sum
-- statement:
--   The Galois Irreducibility construction uses the orbit subset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L72-L74

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Classical

theorem Formalism.GaloisIrreducibility.orbit_subset_sum : OrbitSubSum := by sorry
