-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_orbit_image_eq
-- name    : Formalism.GaloisIrreducibility.orbit_image_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:39.980167+00:00
-- url     : https://prove2.me/theorems/df871873-60ca-4281-a18e-8da0f5a060c0
-- title:
--   Galois Irreducibility: orbit image eq
-- statement:
--   The Galois Irreducibility construction uses the orbit image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L16-L25

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

theorem Formalism.GaloisIrreducibility.orbit_image_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.image f = O := by sorry
