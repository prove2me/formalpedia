-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mul_early_letters_holds
-- name    : Formalism.InvariantFactorPaths.L4.mul_early_letters_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:13.201795+00:00
-- url     : https://prove2.me/theorems/0cec75af-cfe9-4b30-b1ce-6c830b4ed578
-- title:
--   L4: mul early letters holds
-- statement:
--   The L4 construction uses the mul early letters holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L266-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L266-L284

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames

theorem Formalism.InvariantFactorPaths.L4.mul_early_letters_holds : MulEarly := by sorry
