-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_last
-- name    : Formalism.InvariantFactorPaths.L4.pow_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:18.654448+00:00
-- url     : https://prove2.me/theorems/921190e4-b572-4c16-a6d9-9b1d58ba2e35
-- title:
--   L4: pow last
-- statement:
--   The L4 construction uses the pow last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L399-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L399-L426

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

theorem Formalism.InvariantFactorPaths.L4.pow_last (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r) (hc : c ≠ 0)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((glAct p LL j 0 c) ^ (k + 1)) (X (Fin.last K, c) * h) =
      X (Fin.last K, c) * ((glAct p LL j 0 c) ^ (k + 1)) h +
        ((k + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, (0 : Fin r)) * ((glAct p LL j 0 c) ^ k) h) := by sorry
