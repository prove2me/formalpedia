-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_freeOf
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_freeOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:25.678845+00:00
-- url     : https://prove2.me/theorems/7f2897a4-73b3-46fc-b1ca-c1941d6d12f8
-- title:
--   L4: pderiv free Of
-- statement:
--   The L4 construction uses the pderiv free Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L56-L65

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.pderiv_freeOf {σ : Type} (u v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) :
    pderiv u x ∈ FreeOf p v := by sorry
