-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitsFin
-- name    : Formalism.FrobeniusOrbits.hostOrbitsFin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:38.520731+00:00
-- url     : https://prove2.me/theorems/4ff6887d-d220-4915-a54c-c5eba784bcae
-- title:
--   Frobenius Orbits: host Orbits Fin
-- statement:
--   The Frobenius Orbits construction uses the host Orbits Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L176-L177

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
open Orbits

theorem Formalism.FrobeniusOrbits.hostOrbitsFin : HostOrbits ∧ HostOrbitsPlaces ∧ HostOrbitCount ∧ HostFiniteOrder := by sorry
