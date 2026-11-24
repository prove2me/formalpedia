-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_symm_of
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.symm_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:31.755854+00:00
-- url     : https://prove2.me/theorems/1260dc28-bce0-4fa8-8170-88d2115b1576
-- title:
--   Pair Evaluation: symm of
-- statement:
--   The Pair Evaluation construction uses the symm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L213-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L213-L219

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
variable [Algebra ℚ S]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.symm_of {h : MvPolynomial (Fin 2 × Fin d) S} (hs : ev2 h (xs S d 1) (xs S d 0) = h) {τ : Type}
    (u v : Fin d → MvPolynomial τ S) : ev2 h u v = ev2 h v u := by sorry
