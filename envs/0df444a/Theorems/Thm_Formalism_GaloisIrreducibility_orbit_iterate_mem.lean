-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_orbit_iterate_mem
-- name    : Formalism.GaloisIrreducibility.orbit_iterate_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:17.132816+00:00
-- url     : https://prove2.me/theorems/efcc2345-7d72-497d-9c45-0918ced2066c
-- title:
--   Galois Irreducibility: orbit iterate mem
-- statement:
--   The Galois Irreducibility construction uses the orbit iterate mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L7-L14

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

theorem Formalism.GaloisIrreducibility.orbit_iterate_mem {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O)
    {x : α} (hx : x ∈ O) : ∀ n : ℕ, f^[n] x ∈ O := by sorry
