-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Principal_inertia_trivial
-- name    : Formalism.FrobeniusOrbits.Principal.inertia_trivial
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:39:07.203953+00:00
-- url     : https://prove2.me/theorems/24c511c0-70f1-46ef-984f-b72ef71a8d1f
-- title:
--   Principal: inertia trivial
-- statement:
--   The Principal construction uses the inertia trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L34-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L34-L61

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

theorem Formalism.FrobeniusOrbits.Principal.inertia_trivial (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hP0 : P ≠ ⊥)
    (h2 : ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∉ P) (hq : ((q : ℤ) : 𝓞 (hostE ζ a b)) ∉ P)
    (σ : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) : σ = 1 := by sorry
