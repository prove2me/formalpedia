-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_card_pow_eq_one_le_two_mul
-- name    : Formalism.GaloisIrreducibility.card_pow_eq_one_le_two_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:59.330962+00:00
-- url     : https://prove2.me/theorems/4b9d7226-3291-4430-bec0-3315faeed902
-- title:
--   Galois Irreducibility: card pow eq one le two mul
-- statement:
--   The Galois Irreducibility construction uses the card pow eq one le two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L7-L35

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset

theorem Formalism.GaloisIrreducibility.card_pow_eq_one_le_two_mul {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [IsCyclic H] (hH : H.index ≤ 2) {D : ℕ} (hD : 0 < D) :
    #{a : G | a ^ D = 1} ≤ 2 * D := by sorry
