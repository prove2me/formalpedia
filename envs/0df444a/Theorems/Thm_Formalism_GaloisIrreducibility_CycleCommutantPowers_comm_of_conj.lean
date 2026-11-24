-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_comm_of_conj
-- name    : Formalism.GaloisIrreducibility.CycleCommutantPowers.comm_of_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:32.664743+00:00
-- url     : https://prove2.me/theorems/bda21dfa-a657-410b-9e3d-879c01436095
-- title:
--   Cycle Commutant Powers: comm of conj
-- statement:
--   The Cycle Commutant Powers construction uses the comm of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L46-L66

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

theorem Formalism.GaloisIrreducibility.CycleCommutantPowers.comm_of_conj (x y g : Perm α) (u w : ℤ) (hx : x * g * x⁻¹ = g ^ u)
    (hy : y * g * y⁻¹ = g ^ w) :
    (x * y * x⁻¹ * y⁻¹) * g * (x * y * x⁻¹ * y⁻¹)⁻¹ = g := by sorry
