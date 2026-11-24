-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_double
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_double
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:51.694873+00:00
-- url     : https://prove2.me/theorems/655f357c-2d7f-458d-ba69-7a30652b5213
-- title:
--   Pair Evaluation: aeval double
-- statement:
--   The Pair Evaluation construction uses the aeval double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L149-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L149-L168

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable {σ τ : Type}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_double {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j) :
    aeval (fun i => X i + X i) h = C ((2 : S) ^ j) * h := by sorry
