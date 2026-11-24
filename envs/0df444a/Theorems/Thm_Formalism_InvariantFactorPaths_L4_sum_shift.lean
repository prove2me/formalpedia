-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_sum_shift
-- name    : Formalism.InvariantFactorPaths.L4.sum_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:45.320502+00:00
-- url     : https://prove2.me/theorems/919602fc-43cc-4b27-a12d-f7e7753522af
-- title:
--   L4: sum shift
-- statement:
--   The L4 construction uses the sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L190-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L190-L201

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

theorem Formalism.InvariantFactorPaths.L4.sum_shift {σ : Type} [Fintype σ] [DecidableEq σ] (m : σ →₀ ℕ) (u v : σ) (hv : 1 ≤ m v) :
    ∑ w, (Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ) w = ∑ w, m w := by sorry
