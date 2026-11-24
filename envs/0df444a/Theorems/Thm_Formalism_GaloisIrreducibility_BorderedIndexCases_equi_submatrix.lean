-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_equi_submatrix
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.equi_submatrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:37.806324+00:00
-- url     : https://prove2.me/theorems/3085efe6-d620-414b-810d-cd5cac1106ba
-- title:
--   Bordered Index Cases: equi submatrix
-- statement:
--   The Bordered Index Cases construction uses the equi submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L129-L135

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

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.equi_submatrix {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (σ τ : Equiv.Perm (Fin s)) :
    Equi A (A.submatrix σ τ) := by sorry
