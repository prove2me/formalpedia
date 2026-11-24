-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_low_keep
-- name    : Formalism.InvariantFactorPaths.L4.low_keep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:50.944825+00:00
-- url     : https://prove2.me/theorems/3931cf82-6a9e-49ae-9627-ad5e622c5ba9
-- title:
--   L4: low keep
-- statement:
--   The L4 construction uses the low keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L59-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L59-L76

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

theorem Formalism.InvariantFactorPaths.L4.low_keep [NeZero r] (LL : Letters N) (j : ℕ) (a b : Fin r) (ha : a ≠ 0) (M : WithTop ℤ) :
    ∀ x ∈ SuppLE p LL j M, glAct p LL j a b x ∈ SuppLE p LL j M := by sorry
