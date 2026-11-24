-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_jordan_prime_cycle_theorem
-- name    : Formalism.GaloisIrreducibility.jordan_prime_cycle_theorem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:16.241437+00:00
-- url     : https://prove2.me/theorems/55af5bc7-fb37-41df-a052-74f9cb93d6c6
-- title:
--   Galois Irreducibility: jordan prime cycle theorem
-- statement:
--   The Galois Irreducibility construction uses the jordan prime cycle theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L188-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L188-L284

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

theorem Formalism.GaloisIrreducibility.jordan_prime_cycle_theorem : JordanPrime := by sorry
