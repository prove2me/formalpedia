-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_fact_choose_succ
-- name    : Formalism.InvariantFactorPaths.L4.fact_choose_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:33.301494+00:00
-- url     : https://prove2.me/theorems/df83d749-e429-4c03-b9fc-f5c7833afd51
-- title:
--   L4: fact choose succ
-- statement:
--   The L4 construction uses the fact choose succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L45-L51

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem Formalism.InvariantFactorPaths.L4.fact_choose_succ (c : ℤ) (k : ℕ) :
    ((k + 1).factorial : ℤ) * Ring.choose c (k + 1) = c * ((k.factorial : ℤ) * Ring.choose (c - 1) k) := by sorry
