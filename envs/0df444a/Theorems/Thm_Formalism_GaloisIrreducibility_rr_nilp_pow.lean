-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_rr_nilp_pow
-- name    : Formalism.GaloisIrreducibility.rr_nilp_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:29.76896+00:00
-- url     : https://prove2.me/theorems/a7376576-2055-4895-be2b-c10db21c697a
-- title:
--   Galois Irreducibility: rr nilp pow
-- statement:
--   The Galois Irreducibility construction uses the rr nilp pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L37-L45

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

theorem Formalism.GaloisIrreducibility.rr_nilp_pow {R : Type} [Ring R] {K : Type} [Field K] [Algebra K R] (a : R) (c : K)
    (h : IsNilpotent (a - algebraMap K R c)) (q : ℕ) :
    IsNilpotent (a ^ q - algebraMap K R (c ^ q)) := by sorry
