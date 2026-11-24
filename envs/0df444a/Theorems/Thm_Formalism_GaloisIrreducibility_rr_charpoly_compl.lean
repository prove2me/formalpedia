-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_rr_charpoly_compl
-- name    : Formalism.GaloisIrreducibility.rr_charpoly_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:36.114798+00:00
-- url     : https://prove2.me/theorems/b9bcc733-d7e8-4767-8c03-af76c023e3a2
-- title:
--   Galois Irreducibility: rr charpoly compl
-- statement:
--   The Galois Irreducibility construction uses the rr charpoly compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean#L10-L22

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

theorem Formalism.GaloisIrreducibility.rr_charpoly_compl (φ : Module.End K V) (P Q : Submodule K V) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, φ x ∈ P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    φ.charpoly = (φ.restrict hP).charpoly * (φ.restrict hQ).charpoly := by sorry
