-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mulX_ycond
-- name    : Formalism.InvariantFactorPaths.L4.mulX_ycond
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:20.443365+00:00
-- url     : https://prove2.me/theorems/fb9676e3-e76f-4d5c-9147-427f2a29ecd0
-- title:
--   L4: mul X ycond
-- statement:
--   The L4 construction uses the mul X ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L362-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L362-L372

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.mulX_ycond [NeZero r] (LL : Letters (K + 1)) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL K Mt, X (Fin.last K, c) * x ∈ YCond p LL K Mt := by sorry
