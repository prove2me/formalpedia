-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_eq_zpow_on_support
-- name    : Formalism.GaloisIrreducibility.CycleCommutantPowers.eq_zpow_on_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:32.63915+00:00
-- url     : https://prove2.me/theorems/b3e582a2-6e04-4b20-877c-d6d32fdaca15
-- title:
--   Cycle Commutant Powers: eq zpow on support
-- statement:
--   The Cycle Commutant Powers construction uses the eq zpow on support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L68-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L68-L88

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Equiv Equiv.Perm MulAction
open Formalism.GaloisIrreducibility.CycleCommutantPowers
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Formalism.GaloisIrreducibility.CycleCommutantPowers.eq_zpow_on_support (g z : Perm α) (hg : g.IsCycle) (hz : z * g = g * z) :
    ∃ j : ℤ, ∀ d, g d ≠ d → z d = (g ^ j) d := by sorry
