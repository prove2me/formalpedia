-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_conj_key
-- name    : Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:34.398847+00:00
-- url     : https://prove2.me/theorems/fb502981-f576-4cda-a398-62ee29657979
-- title:
--   Cycle Commutant Powers: conj key
-- statement:
--   The Cycle Commutant Powers construction uses the conj key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L40-L44

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

theorem Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_key (c g : Perm α) (e : ℤ) (hc : c * g * c⁻¹ = g ^ e) (m : ℤ) :
    c * g ^ m * c⁻¹ = g ^ (e * m) := by sorry
