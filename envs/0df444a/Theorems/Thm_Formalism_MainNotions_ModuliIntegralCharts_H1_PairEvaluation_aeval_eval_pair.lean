-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_eval_pair
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_eval_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:57.232017+00:00
-- url     : https://prove2.me/theorems/4bccdd9e-8dbf-424a-bac4-d638c0bcff53
-- title:
--   Pair Evaluation: aeval eval pair
-- statement:
--   The Pair Evaluation construction uses the aeval eval pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L32-L41

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_eval_pair {τ τ' : Type} (g : τ → MvPolynomial τ' S) (h : MvPolynomial (Fin 2 × Fin d) S)
    (u v : Fin d → MvPolynomial τ S) :
    aeval g (ev2 h u v) = ev2 h (fun i => aeval g (u i)) (fun i => aeval g (v i)) := by sorry
