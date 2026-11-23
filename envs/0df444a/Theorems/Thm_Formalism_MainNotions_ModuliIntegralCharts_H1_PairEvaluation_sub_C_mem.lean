-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_sub_C_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.sub_C_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:42.066847+00:00
-- url     : https://prove2.me/theorems/b0fb5a7a-0008-4b7f-bedd-aa322fd67e85
-- title:
--   Pair Evaluation: sub C mem
-- statement:
--   The Pair Evaluation construction uses the sub C mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L63-L68

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.sub_C_mem (p : MvPolynomial σ S) : p - C (coeff 0 p) ∈ Io S σ := by sorry
