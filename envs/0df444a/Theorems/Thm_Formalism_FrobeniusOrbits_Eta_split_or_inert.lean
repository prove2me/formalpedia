-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Eta_split_or_inert
-- name    : Formalism.FrobeniusOrbits.Eta.split_or_inert
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:08.916119+00:00
-- url     : https://prove2.me/theorems/0a979de5-3c9a-4049-8e53-0378fd3481de
-- title:
--   Eta: split or inert
-- statement:
--   The Eta construction uses the split or inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/NcardEqTwoIff.lean#L47-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/NcardEqTwoIff.lean#L47-L83

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

theorem Formalism.FrobeniusOrbits.Eta.split_or_inert
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (𝔭 : Ideal (𝓞 K⁺)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (primesOver 𝔭 (𝓞 K)).ncard = 2 ∨
      ((primesOver 𝔭 (𝓞 K)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 K) = 2) := by sorry
