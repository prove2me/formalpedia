-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_ycond_early
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_ycond_early
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:35.564748+00:00
-- url     : https://prove2.me/theorems/58a4ad1c-a22e-4852-a981-3edea61743f2
-- title:
--   L4: pderiv ycond early
-- statement:
--   The L4 construction uses the pderiv ycond early property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L76-L79

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

theorem Formalism.InvariantFactorPaths.L4.pderiv_ycond_early [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (hj : j ≤ K) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j Mt, pderiv (Fin.last K, c) x ∈ YCond p LL j Mt := by sorry
