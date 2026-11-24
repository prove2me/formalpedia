-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_one
-- name    : Formalism.InvariantFactorPaths.L4.glAct_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:52.132203+00:00
-- url     : https://prove2.me/theorems/86ca0ddc-631a-44c3-9954-daef99bbab54
-- title:
--   L4: gl Act one
-- statement:
--   The L4 construction uses the gl Act one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L30-L45

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos
import Theorems.Thm_Formalism_GM_M_FB_glAct_one

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

theorem Formalism.InvariantFactorPaths.L4.glAct_one (LL : Letters N) (i0 : Fin N) (h0 : (i0 : ℕ) = 0) (c d : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL 1 c d x =
      if LL.vec i0 then X (i0, c) * pderiv (i0, d) x else -(X (i0, d) * pderiv (i0, c) x) := by sorry
