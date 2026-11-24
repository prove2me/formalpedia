-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_le_ram
-- name    : Formalism.FrobeniusOrbits.Mu.mu_le_ram
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:51.544058+00:00
-- url     : https://prove2.me/theorems/984ec8be-b89e-4a83-b864-28a9285e1919
-- title:
--   Mu: mu le ram
-- statement:
--   The Mu construction uses the mu le ram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L19-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L19-L42

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

theorem Formalism.FrobeniusOrbits.Mu.mu_le_ram (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (k : ℕ) (hk : ((p : ℤ) : 𝓞 L) ∈ Q ^ k) :
    k ≤ Q.ramificationIdx ℤ := by sorry
