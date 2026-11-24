-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_ram_bound
-- name    : Formalism.FrobeniusOrbits.Mu.mu_ram_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:11:02.052894+00:00
-- url     : https://prove2.me/theorems/d6910385-129c-434a-88d7-13a607960dc1
-- title:
--   Mu: mu ram bound
-- statement:
--   The Mu construction uses the mu ram bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L105-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L105-L161

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
variable {e q d : ℕ} {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Mu.mu_ram_bound (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    Q.ramificationIdx ℤ ≤ 2 ∧ (p ≠ q → p ≠ d → Q.ramificationIdx ℤ ≤ 1) := by sorry
