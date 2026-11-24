-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_lin_add_lin
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.lin_add_lin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:33.03821+00:00
-- url     : https://prove2.me/theorems/5ed6c682-c184-427a-8fcf-16ad692cb357
-- title:
--   Pair Evaluation: lin add lin
-- statement:
--   The Pair Evaluation construction uses the lin add lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L221-L225

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.lin_add_lin (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0) {n : ℕ}
    (k : Fin n) : (fun i => lin A k i + lin Ab k i) = xs S d k := by sorry
