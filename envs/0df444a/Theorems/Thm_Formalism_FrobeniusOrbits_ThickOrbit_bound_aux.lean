-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_bound_aux
-- name    : Formalism.FrobeniusOrbits.ThickOrbit.bound_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:10.075743+00:00
-- url     : https://prove2.me/theorems/a6fad630-8a27-477b-9b0e-8edce4425777
-- title:
--   Thick Orbit: bound aux
-- statement:
--   The Thick Orbit construction uses the bound aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L9-L13

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

theorem Formalism.FrobeniusOrbits.ThickOrbit.bound_aux {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ L) (hs : 4 * L * s < n) :
    4 * (j * (s : ℤ)) < n := by sorry
