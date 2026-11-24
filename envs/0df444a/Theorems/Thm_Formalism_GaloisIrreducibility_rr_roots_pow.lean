-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_rr_roots_pow
-- name    : Formalism.GaloisIrreducibility.rr_roots_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:31.524067+00:00
-- url     : https://prove2.me/theorems/a0060478-ee20-417c-94a1-0b4384368ae0
-- title:
--   Galois Irreducibility: rr roots pow
-- statement:
--   The Galois Irreducibility construction uses the rr roots pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L56-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L56-L131

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

theorem Formalism.GaloisIrreducibility.rr_roots_pow {K : Type} [Field K] [IsAlgClosed K] (q : ℕ) : ∀ (n : ℕ) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    finrank K V = n → ∀ (A : Module.End K V),
      (A ^ q).charpoly.roots = A.charpoly.roots.map (· ^ q) := by sorry
