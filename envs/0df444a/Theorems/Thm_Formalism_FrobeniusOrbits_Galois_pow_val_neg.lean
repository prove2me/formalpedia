-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_pow_val_neg
-- name    : Formalism.FrobeniusOrbits.Galois.pow_val_neg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:53:24.243805+00:00
-- url     : https://prove2.me/theorems/5761e131-6420-4265-8b2d-ee95a5cb4bf1
-- title:
--   Galois: pow val neg
-- statement:
--   The Galois construction uses the pow val neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L32-L35

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
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}

theorem Formalism.FrobeniusOrbits.Galois.pow_val_neg (hζ : IsPrimitiveRoot ζ N) (k : ZMod N) :
    ζ ^ (-k).val = ζ⁻¹ ^ k.val := by sorry
