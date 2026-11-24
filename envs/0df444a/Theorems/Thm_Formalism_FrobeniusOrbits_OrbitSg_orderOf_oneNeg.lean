-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_orderOf_oneNeg
-- name    : Formalism.FrobeniusOrbits.OrbitSg.orderOf_oneNeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:31:19.713496+00:00
-- url     : https://prove2.me/theorems/96502e5d-6fc0-4ced-a1e4-18598ac0e7fe
-- title:
--   Orbit Sg: order Of one Neg
-- statement:
--   The Orbit Sg construction uses the order Of one Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.OrbitSg

theorem Formalism.FrobeniusOrbits.OrbitSg.orderOf_oneNeg : orderOf (((1 : ℤˣ), (-1 : ℤˣ)) : G0) = 2 := by sorry
