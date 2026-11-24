-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_finrank_hostF
-- name    : Formalism.FrobeniusOrbits.finrank_hostF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:23.541928+00:00
-- url     : https://prove2.me/theorems/7894a6ca-6441-4e18-83cb-a469b9a89f79
-- title:
--   Frobenius Orbits: finrank host F
-- statement:
--   The Frobenius Orbits construction uses the finrank host F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L319-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L319-L320

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.finrank_hostF (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) := by sorry
