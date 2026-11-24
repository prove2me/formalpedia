-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_rank_map
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.Equi.rank_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:09.150246+00:00
-- url     : https://prove2.me/theorems/d8a37c15-b17d-437f-9b54-05b175328421
-- title:
--   Equi: rank map
-- statement:
--   The Equi construction uses the rank map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L106-L115

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.Equi.rank_map {K : Type} [Field K] (φ : R →+* K) {s : ℕ}
    {A B : Matrix (Fin s) (Fin s) R} (h : Equi A B) : (B.map φ).rank = (A.map φ).rank := by sorry
