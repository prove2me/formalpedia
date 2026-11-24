-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eq_zero_of_isHomogeneous
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eq_zero_of_isHomogeneous
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:58.281342+00:00
-- url     : https://prove2.me/theorems/d2e01d19-248b-4427-9b90-8f47e101bf19
-- title:
--   Pair Evaluation: eq zero of is Homogeneous
-- statement:
--   The Pair Evaluation construction uses the eq zero of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L127-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L127-L137

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eq_zero_of_isHomogeneous {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j)
    (hm : h ∈ Io S σ ^ (j + 1)) : h = 0 := by sorry
