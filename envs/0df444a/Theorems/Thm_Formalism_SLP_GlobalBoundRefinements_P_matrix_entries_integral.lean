-- Prove2me | Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_matrix_entries_integral
-- name    : Formalism.SLP.GlobalBoundRefinements.P.matrix_entries_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:40.985118+00:00
-- url     : https://prove2.me/theorems/d0e66e5c-c318-4106-b48e-c0c2788a2213
-- title:
--   P: matrix entries integral
-- statement:
--   The P construction uses the matrix entries integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/ArithmeticLatticeHypothesis.lean#L6-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/ArithmeticLatticeHypothesis.lean#L6-L20

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements

theorem Formalism.SLP.GlobalBoundRefinements.P.matrix_entries_integral (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.conjTranspose * J * M = J) :
    ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 = 1 ∧ ‖M 0 1‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 ∧
      ‖M 0 0‖ * ‖M 0 1‖ = ‖M 1 0‖ * ‖M 1 1‖ := by sorry
