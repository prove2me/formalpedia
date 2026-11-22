-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_snoc
-- name    : Formalism.InvariantFactorPaths.L4.wd_snoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:59.672014+00:00
-- url     : https://prove2.me/theorems/af84f7c1-7c0b-4a80-aa2f-843899b03898
-- title:
--   L4: wd snoc
-- statement:
--   The L4 construction uses the wd snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L28-L32

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

theorem Formalism.InvariantFactorPaths.L4.wd_snoc [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (l : List (Fin r))
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wd p LL j (l ++ [c]) F = wd p LL j l (glAct p LL j 0 c F) := by sorry
