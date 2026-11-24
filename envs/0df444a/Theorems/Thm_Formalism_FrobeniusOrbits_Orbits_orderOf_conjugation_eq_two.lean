-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Orbits_orderOf_conjugation_eq_two
-- name    : Formalism.FrobeniusOrbits.Orbits.orderOf_conjugation_eq_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:55.157414+00:00
-- url     : https://prove2.me/theorems/a7a9f32b-a390-49e3-8a95-3464961d00b5
-- title:
--   Orbits: order Of conjugation eq two
-- statement:
--   The Orbits construction uses the order Of conjugation eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L14-L20

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Orbits

theorem Formalism.FrobeniusOrbits.Orbits.orderOf_conjugation_eq_two : orderOf c0 = 2 := by sorry
