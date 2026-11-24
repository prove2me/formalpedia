-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
-- name    : Formalism.FrobeniusOrbits.ThickOrbit.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:44.696436+00:00
-- url     : https://prove2.me/theorems/1d2a2db6-1632-4ee9-a8ce-6a9142816fb0
-- title:
--   Thick Orbit: key
-- statement:
--   The Thick Orbit construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L21-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean#L21-L69

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

theorem Formalism.FrobeniusOrbits.ThickOrbit.key {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ a b c : ℤ)
    (ha : a ∈ Finset.Ico i₀ (i₀ + L)) (hc : c ∈ Finset.Ico i₀ (i₀ + L)) (hab : a < b)
    (hbc : b < c) (hxa : InTranslate T u₀ (t + a • h)) (hxb : InTranslate T u₀ (t + b • h))
    (hxc : InTranslate T u₀ (t + c • h)) : False := by sorry
