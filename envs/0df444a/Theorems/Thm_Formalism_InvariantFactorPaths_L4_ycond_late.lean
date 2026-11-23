-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_late
-- name    : Formalism.InvariantFactorPaths.L4.ycond_late
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:21.117481+00:00
-- url     : https://prove2.me/theorems/68645d5b-eb54-409b-b65b-8f30f952a4ab
-- title:
--   L4: ycond late
-- statement:
--   The L4 construction uses the ycond late property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L168-L170

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

theorem Formalism.InvariantFactorPaths.L4.ycond_late [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (hj : K + 1 ≤ j) (Mt : WithTop ℤ) :
    YCond p (r := r) LL j Mt = YCond p LL (K + 1) Mt := by sorry
