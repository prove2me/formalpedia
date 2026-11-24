-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_int_mul_lt_of_le_four_mul
-- name    : Formalism.FrobeniusOrbits.ThickOrbit.int_mul_lt_of_le_four_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:06.035977+00:00
-- url     : https://prove2.me/theorems/e85011f8-bf8e-47d9-8585-b456cc2496c2
-- title:
--   Thick Orbit: int mul lt of le four mul
-- statement:
--   The Thick Orbit construction uses the int mul lt of le four mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.ThickOrbit

theorem Formalism.FrobeniusOrbits.ThickOrbit.int_mul_lt_of_le_four_mul {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ 4 * L) (hs : 4 * L * s < n) :
    j * (s : ℤ) < n := by sorry
