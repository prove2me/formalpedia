-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_conj_pow_eq
-- name    : Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:45.269484+00:00
-- url     : https://prove2.me/theorems/3e492c4d-14f2-4545-b05f-0311e5339ae5
-- title:
--   Cycle Commutant Powers: conj pow eq
-- statement:
--   The Cycle Commutant Powers construction uses the conj pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L11-L27

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

theorem Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_pow_eq (x g : Perm α) (u : ℤ) (hx : x * g * x⁻¹ = g ^ u) :
    ∀ n : ℕ, x ^ n * g * (x ^ n)⁻¹ = g ^ (u ^ n) := by sorry
