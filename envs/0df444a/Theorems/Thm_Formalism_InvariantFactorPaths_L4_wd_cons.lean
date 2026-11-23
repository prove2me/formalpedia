-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_cons
-- name    : Formalism.InvariantFactorPaths.L4.wd_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:01.233155+00:00
-- url     : https://prove2.me/theorems/eebc01f0-d13a-43bc-bd0e-1f55fd7cadad
-- title:
--   L4: wd cons
-- statement:
--   The L4 construction uses the wd cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L23-L26

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

theorem Formalism.InvariantFactorPaths.L4.wd_cons [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (l : List (Fin r))
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wd p LL j (c :: l) F = glAct p LL j 0 c (wd p LL j l F) := by sorry
