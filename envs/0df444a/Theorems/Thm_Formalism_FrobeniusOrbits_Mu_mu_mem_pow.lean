-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_mem_pow
-- name    : Formalism.FrobeniusOrbits.Mu.mu_mem_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:11:02.81253+00:00
-- url     : https://prove2.me/theorems/244d6fba-b83b-44ac-bf1c-fd6596cac4f6
-- title:
--   Mu: mu mem pow
-- statement:
--   The Mu construction uses the mu mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L44-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L44-L92

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo
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
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.FrobeniusOrbits.Mu.mu_mem_pow (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (η : L) (hη : IsPrimitiveRoot η p) :
    ((p : ℤ) : 𝓞 L) ∈ Q ^ (p - 1) := by sorry
