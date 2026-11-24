-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Principal_galE_restrict_mem_Psi
-- name    : Formalism.FrobeniusOrbits.Principal.galE_restrict_mem_Psi
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:39:06.441107+00:00
-- url     : https://prove2.me/theorems/8e480e6f-4e5f-43e0-bc7b-39f1aafd8e68
-- title:
--   Principal: gal E restrict mem Psi
-- statement:
--   The Principal construction uses the gal E restrict mem Psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L25-L32

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Principal.galE_restrict_mem_Psi (σ : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) :
    galE e ζ a b (σ.restrictScalars ℚ) ∈ Psi e := by sorry
