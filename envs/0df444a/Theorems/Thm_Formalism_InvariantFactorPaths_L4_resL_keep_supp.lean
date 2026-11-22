-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_keep_supp
-- name    : Formalism.InvariantFactorPaths.L4.resL_keep_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:50.658199+00:00
-- url     : https://prove2.me/theorems/9557627a-78c3-403e-a989-0e130924c7f2
-- title:
--   L4: res L keep supp
-- statement:
--   The L4 construction uses the res L keep supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L11-L22

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.L4.resL_keep_supp (v : σ) (e : ℕ) (Q : Set (σ →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, resL p v e x ∈ restrictSupport ℚ_[p] Q := by sorry
