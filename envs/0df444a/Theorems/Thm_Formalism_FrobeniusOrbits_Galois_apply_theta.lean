-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_apply_theta
-- name    : Formalism.FrobeniusOrbits.Galois.apply_theta
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:28.143018+00:00
-- url     : https://prove2.me/theorems/5a00c8f4-4bd3-4fc3-a552-5ffbbec4affa
-- title:
--   Galois: apply theta
-- statement:
--   The Galois construction uses the apply theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L138-L140

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Galois.apply_theta {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) (τ : Gal(L/ℚ)) :
    τ (ζ + ζ⁻¹) = ζ ^ (hζ.autToPow ℚ τ : ZMod N).val + ζ⁻¹ ^ (hζ.autToPow ℚ τ : ZMod N).val := by sorry
