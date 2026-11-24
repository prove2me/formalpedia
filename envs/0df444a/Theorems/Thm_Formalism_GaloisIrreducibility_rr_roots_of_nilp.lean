-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_rr_roots_of_nilp
-- name    : Formalism.GaloisIrreducibility.rr_roots_of_nilp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:29.206651+00:00
-- url     : https://prove2.me/theorems/c26044e6-1228-4c59-86d5-e117d32056ca
-- title:
--   Galois Irreducibility: rr roots of nilp
-- statement:
--   The Galois Irreducibility construction uses the rr roots of nilp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L24-L33

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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem Formalism.GaloisIrreducibility.rr_roots_of_nilp (B : Module.End K V) (c : K) (h : IsNilpotent (B - c • 1)) :
    B.charpoly.roots = Multiset.replicate (finrank K V) c := by sorry
