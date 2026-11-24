-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_no_odd
-- name    : Formalism.FrobeniusOrbits.Mu.mu_no_odd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:36.432124+00:00
-- url     : https://prove2.me/theorems/635f3427-a391-4f50-8aec-d8cf4366798b
-- title:
--   Mu: mu no odd
-- statement:
--   The Mu construction uses the mu no odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L163-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean#L163-L183

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

theorem Formalism.FrobeniusOrbits.Mu.mu_no_odd (hq : HostHyp q d) (hq3 : q ≠ 3) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (η : L) (hη : IsPrimitiveRoot η p) : False := by sorry
