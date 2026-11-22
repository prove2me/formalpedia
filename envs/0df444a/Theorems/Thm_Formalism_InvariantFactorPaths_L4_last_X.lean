-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X
-- name    : Formalism.InvariantFactorPaths.L4.last_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:51.700848+00:00
-- url     : https://prove2.me/theorems/1bf7fa6c-f483-418f-b663-2fd440b1a726
-- title:
--   L4: last X
-- statement:
--   The L4 construction uses the last X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L290-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L290-L294

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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.last_X (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (a b c : Fin r) :
    glAct p LL j a b (X (Fin.last K, c)) = if b = c then X (Fin.last K, a) else 0 := by sorry
