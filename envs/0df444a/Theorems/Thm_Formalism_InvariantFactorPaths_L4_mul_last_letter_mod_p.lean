-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mul_last_letter_mod_p
-- name    : Formalism.InvariantFactorPaths.L4.mul_last_letter_mod_p
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:17.273534+00:00
-- url     : https://prove2.me/theorems/121889a7-7611-4df9-b73d-6fec6c111537
-- title:
--   L4: mul last letter mod p
-- statement:
--   The L4 construction uses the mul last letter mod p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L308-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L308-L338

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem Formalism.InvariantFactorPaths.L4.mul_last_letter_mod_p : MulLastModP := by sorry
