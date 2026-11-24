-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_orbit_map_eq
-- name    : Formalism.GaloisIrreducibility.orbit_map_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:25.157479+00:00
-- url     : https://prove2.me/theorems/c1e8d3f0-80cb-4956-aec8-795aca37d873
-- title:
--   Galois Irreducibility: orbit map eq
-- statement:
--   The Galois Irreducibility construction uses the orbit map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L27-L31

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

theorem Formalism.GaloisIrreducibility.orbit_map_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.val.map f = O.val := by sorry
