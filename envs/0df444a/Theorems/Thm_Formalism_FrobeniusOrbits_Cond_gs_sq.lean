-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq
-- name    : Formalism.FrobeniusOrbits.Cond.gs_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:11:21.75787+00:00
-- url     : https://prove2.me/theorems/3c9ac421-9dcf-4cea-86ab-1678c3b75071
-- title:
--   Cond: gs sq
-- statement:
--   The Cond construction uses the gs sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L36-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L36-L51

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
variable {K : Type*} [Field K] [CharZero K]

theorem Formalism.FrobeniusOrbits.Cond.gs_sq {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : IsPrimitiveRoot x p) :
    gs p hx.pow_eq_one ^ 2 = -(p : K) := by sorry
