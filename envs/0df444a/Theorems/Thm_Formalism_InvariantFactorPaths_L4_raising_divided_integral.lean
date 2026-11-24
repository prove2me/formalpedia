-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_divided_integral
-- name    : Formalism.InvariantFactorPaths.L4.raising_divided_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:23.087559+00:00
-- url     : https://prove2.me/theorems/d55f5d7d-084b-4fc6-a97e-12959dc7c1fe
-- title:
--   L4: raising divided integral
-- statement:
--   The L4 construction uses the raising divided integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L434-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L434-L437

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

theorem Formalism.InvariantFactorPaths.L4.raising_divided_integral : UDivInt := by sorry
