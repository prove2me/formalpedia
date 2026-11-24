-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Eta_card_gal
-- name    : Formalism.FrobeniusOrbits.Eta.card_gal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:22.615744+00:00
-- url     : https://prove2.me/theorems/77f31c76-1c64-4cbe-88eb-7b4081c7d9f2
-- title:
--   Eta: card gal
-- statement:
--   The Eta construction uses the card gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/NcardEqTwoIff.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/NcardEqTwoIff.lean#L40-L42

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff
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
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Eta
variable (K : Type) [Field K] [NumberField K] [IsCMField K]
local notation3 "K⁺" => maximalRealSubfield K

theorem Formalism.FrobeniusOrbits.Eta.card_gal : Nat.card (K ≃ₐ[K⁺] K) = 2 := by sorry
