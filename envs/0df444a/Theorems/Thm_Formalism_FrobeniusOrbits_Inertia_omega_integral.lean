-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_omega_integral
-- name    : Formalism.FrobeniusOrbits.Inertia.omega_integral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:07.522985+00:00
-- url     : https://prove2.me/theorems/ed8ced6f-ff56-41c2-ad62-da28b5d3259d
-- title:
--   Inertia: omega integral
-- statement:
--   The Inertia construction uses the omega integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L42-L51

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia

theorem Formalism.FrobeniusOrbits.Inertia.omega_integral {F : Type} [Field F] [NumberField F] {r : ℕ} (hr4 : r % 4 = 3) {X : F}
    (hX : X ^ 2 = -(r : F)) : IsIntegral ℤ ((1 + X) / 2) := by sorry
