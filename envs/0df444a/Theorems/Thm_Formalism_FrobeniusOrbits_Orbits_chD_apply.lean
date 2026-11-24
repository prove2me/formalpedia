-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Orbits_chD_apply
-- name    : Formalism.FrobeniusOrbits.Orbits.chD_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:38.863486+00:00
-- url     : https://prove2.me/theorems/1c49aaf6-26b0-43b3-bfe8-1ac8ee1d73ca
-- title:
--   Orbits: ch D apply
-- statement:
--   The Orbits construction uses the ch D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L22-L22

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

theorem Formalism.FrobeniusOrbits.Orbits.chD_apply (e : ℕ) (g : GG e) : chD e g = g.1.2 := by sorry
