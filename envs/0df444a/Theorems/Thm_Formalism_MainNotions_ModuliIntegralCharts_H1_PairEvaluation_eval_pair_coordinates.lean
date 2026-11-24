-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_coordinates
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_coordinates
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:11.814581+00:00
-- url     : https://prove2.me/theorems/f40236e7-27db-462e-988d-033396c23f90
-- title:
--   Pair Evaluation: eval pair coordinates
-- statement:
--   The Pair Evaluation construction uses the eval pair coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L24-L30

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_coordinates (h : MvPolynomial (Fin 2 × Fin d) S) : ev2 h (xs S d 0) (xs S d 1) = h := by sorry
