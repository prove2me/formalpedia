-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_map
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.bord_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:15.162116+00:00
-- url     : https://prove2.me/theorems/9a39ba66-2c6d-4730-9b39-47059d131cc8
-- title:
--   Bordered Index Cases: bord map
-- statement:
--   The Bordered Index Cases construction uses the bord map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L56-L60

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
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.bord_map {S : Type} [CommRing S] (φ : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (bord M).map φ = bord (M.map φ) := by sorry
