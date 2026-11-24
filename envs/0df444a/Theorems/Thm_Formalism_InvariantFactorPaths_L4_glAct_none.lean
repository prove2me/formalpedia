-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_none
-- name    : Formalism.InvariantFactorPaths.L4.glAct_none
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:51.398508+00:00
-- url     : https://prove2.me/theorems/5255c775-71c5-466e-bd43-00ee6c1109f3
-- title:
--   L4: gl Act none
-- statement:
--   The L4 construction uses the gl Act none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L22-L24

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.glAct_none (LL : Letters N) (j : ℕ) (h : ∀ i : Fin N, ¬ (i : ℕ) < j) (c d : Fin r) :
    glAct p LL j c d = 0 := by sorry
