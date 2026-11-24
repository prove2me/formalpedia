-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_free_ycond_succ
-- name    : Formalism.InvariantFactorPaths.L4.free_ycond_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:42.529946+00:00
-- url     : https://prove2.me/theorems/4829b65a-2fae-4a04-9645-22c943612ebe
-- title:
--   L4: free ycond succ
-- statement:
--   The L4 construction uses the free ycond succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L172-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L172-L196

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

theorem Formalism.InvariantFactorPaths.L4.free_ycond_succ [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    YCond p LL K Mt ⊓ FreeLast p K r ≤ YCond p LL (K + 1) Mt := by sorry
