-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_one
-- name    : Formalism.InvariantFactorPaths.L4.wt_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:13.904683+00:00
-- url     : https://prove2.me/theorems/5a79d8b8-b058-4710-b2c0-15098e1bc4af
-- title:
--   L4: wt one
-- statement:
--   The L4 construction uses the wt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L47-L58

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

theorem Formalism.InvariantFactorPaths.L4.wt_one (LL : Letters N) (i0 : Fin N) (h0 : (i0 : ℕ) = 0) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL 1 c m = if LL.vec i0 then (m (i0, c) : ℤ) else -(m (i0, c) : ℤ) := by sorry
