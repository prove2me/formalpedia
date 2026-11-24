-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mulLast_bwd
-- name    : Formalism.InvariantFactorPaths.L4.mulLast_bwd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:21.346801+00:00
-- url     : https://prove2.me/theorems/98644d6e-f435-42a9-aa22-5fa9fd2deedb
-- title:
--   L4: mul Last bwd
-- statement:
--   The L4 construction uses the mul Last bwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L302-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L302-L343

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

theorem Formalism.InvariantFactorPaths.L4.mulLast_bwd (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hh : h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ))) :
    X (Fin.last K, c) * h ∈ YCond p LL j M := by sorry
