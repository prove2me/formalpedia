-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_part_one
-- name    : Formalism.FrobeniusOrbits.ThickOrbit.part_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:13.9698+00:00
-- url     : https://prove2.me/theorems/a2d5976d-e416-4326-a8cf-feff9b2cefe7
-- title:
--   Thick Orbit: part one
-- statement:
--   The Thick Orbit construction uses the part one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L71-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L71-L94

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

theorem Formalism.FrobeniusOrbits.ThickOrbit.part_one {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ : ℤ) :
    ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h))).card ≤ 2 := by sorry
