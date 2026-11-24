-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_sub_mem_sq
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_sub_mem_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:55.862421+00:00
-- url     : https://prove2.me/theorems/6d11f641-d07b-4fbe-aa1e-80e3b91e4fc2
-- title:
--   Pair Evaluation: aeval sub mem sq
-- statement:
--   The Pair Evaluation construction uses the aeval sub mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L78-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L78-L100

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_sub_mem_sq (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) {p : MvPolynomial σ S} (hp : p ∈ Io S σ) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by sorry
