-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_additive_first
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_additive_first
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:53.248967+00:00
-- url     : https://prove2.me/theorems/daa64e0e-f23d-4132-85dd-c31c79e8b7d9
-- title:
--   Pair Evaluation: eval pair additive first
-- statement:
--   The Pair Evaluation construction uses the eval pair additive first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L195-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L195-L211

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_additive_first {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    {τ : Type} (u u' v : Fin d → MvPolynomial τ S) :
    ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := by sorry
