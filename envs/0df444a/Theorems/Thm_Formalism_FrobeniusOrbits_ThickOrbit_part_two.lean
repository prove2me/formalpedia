-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_part_two
-- name    : Formalism.FrobeniusOrbits.ThickOrbit.part_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:32.386262+00:00
-- url     : https://prove2.me/theorems/f4e05157-591e-4e7a-80de-e0efb3e72149
-- title:
--   Thick Orbit: part two
-- statement:
--   The Thick Orbit construction uses the part two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L96-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L96-L128

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

theorem Formalism.FrobeniusOrbits.ThickOrbit.part_two {n L : ℕ} (hn : 0 < n) (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n)
    (u₀ t h : ZMod n) (hord : addOrderOf h ≤ 4 * L) :
    {x : ZMod n | (∃ i : ℤ, x = t + i • h) ∧ InTranslate T u₀ x}.ncard ≤ 1 := by sorry
