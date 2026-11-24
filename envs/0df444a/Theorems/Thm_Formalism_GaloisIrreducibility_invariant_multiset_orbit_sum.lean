-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_invariant_multiset_orbit_sum
-- name    : Formalism.GaloisIrreducibility.invariant_multiset_orbit_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:04.027013+00:00
-- url     : https://prove2.me/theorems/cc5bca2e-d483-4ac0-ab86-4baf57054114
-- title:
--   Galois Irreducibility: invariant multiset orbit sum
-- statement:
--   The Galois Irreducibility construction uses the invariant multiset orbit sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L45-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OrbitSubSum.lean#L45-L70

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

theorem Formalism.GaloisIrreducibility.invariant_multiset_orbit_sum {α ι : Type} (f : α → α) (O : ι → Finset α) (I : Finset ι) :
    ∀ (M' : Multiset α), (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val →
      M'.map f = M' → ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card := by sorry
