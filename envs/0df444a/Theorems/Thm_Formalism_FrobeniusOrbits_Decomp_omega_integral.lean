-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_omega_integral
-- name    : Formalism.FrobeniusOrbits.Decomp.omega_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:29.376236+00:00
-- url     : https://prove2.me/theorems/91ee5fd3-691d-4b42-b07d-cd9a36a60887
-- title:
--   Decomp: omega integral
-- statement:
--   The Decomp construction uses the omega integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L302-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L302-L309

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Decomp.omega_integral {F : Type} [Field F] [NumberField F] {r : ℕ} (hr4 : r % 4 = 3) {X : F}
    (hX : X ^ 2 = -(r : F)) : IsIntegral ℤ ((1 + X) / 2) := by sorry
