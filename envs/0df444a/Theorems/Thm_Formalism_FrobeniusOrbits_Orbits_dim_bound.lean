-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Orbits_dim_bound
-- name    : Formalism.FrobeniusOrbits.Orbits.dim_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:10:45.531796+00:00
-- url     : https://prove2.me/theorems/12b04c3c-4c50-4bc1-b8b7-61fe42bf7445
-- title:
--   Orbits: dim bound
-- statement:
--   The Orbits construction uses the dim bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L46-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean#L46-L91

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

theorem Formalism.FrobeniusOrbits.Orbits.dim_bound {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ Module.finrank ℚ E * k := by sorry
