-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_perm_isUnit
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.perm_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:32.358899+00:00
-- url     : https://prove2.me/theorems/1e0f7ee1-3a76-4c78-8d5b-2239b2ccf36a
-- title:
--   Bordered Index Cases: perm is Unit
-- statement:
--   The Bordered Index Cases construction uses the perm is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L117-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L117-L127

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

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.perm_isUnit {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin s) (Fin s) R) := by sorry
