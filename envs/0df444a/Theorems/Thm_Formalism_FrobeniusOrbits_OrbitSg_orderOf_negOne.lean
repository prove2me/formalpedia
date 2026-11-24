-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_orderOf_negOne
-- name    : Formalism.FrobeniusOrbits.OrbitSg.orderOf_negOne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:31:32.440802+00:00
-- url     : https://prove2.me/theorems/34fb721b-8b43-4109-86ec-7ddc2cb29525
-- title:
--   Orbit Sg: order Of neg One
-- statement:
--   The Orbit Sg construction uses the order Of neg One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L11-L13

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

theorem Formalism.FrobeniusOrbits.OrbitSg.orderOf_negOne : orderOf (-1 : ℤˣ) = 2 := by sorry
