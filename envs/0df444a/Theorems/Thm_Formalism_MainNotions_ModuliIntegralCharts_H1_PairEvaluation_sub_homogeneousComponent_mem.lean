-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_sub_homogeneousComponent_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.sub_homogeneousComponent_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:13.377051+00:00
-- url     : https://prove2.me/theorems/4564f553-1ac5-4a7d-bbca-e4ff643a711e
-- title:
--   Pair Evaluation: sub homogeneous Component mem
-- statement:
--   The Pair Evaluation construction uses the sub homogeneous Component mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L139-L147

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.sub_homogeneousComponent_mem {W : MvPolynomial σ S} {j : ℕ} (hW : W ∈ Io S σ ^ j) :
    W - homogeneousComponent j W ∈ Io S σ ^ (j + 1) := by sorry
