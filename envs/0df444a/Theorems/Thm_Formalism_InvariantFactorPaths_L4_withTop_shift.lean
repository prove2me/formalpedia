-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_withTop_shift
-- name    : Formalism.InvariantFactorPaths.L4.withTop_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:07.103021+00:00
-- url     : https://prove2.me/theorems/d5197bfd-1632-476c-a6c5-f4641e2d9479
-- title:
--   L4: with Top shift
-- statement:
--   The L4 construction uses the with Top shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L256-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L256-L262

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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.withTop_shift (w : ℤ) (M : WithTop ℤ) :
    ((w + 1 : ℤ) : WithTop ℤ) ≤ M ↔ ((w : ℤ) : WithTop ℤ) ≤ M + ((-1 : ℤ) : WithTop ℤ) := by sorry
