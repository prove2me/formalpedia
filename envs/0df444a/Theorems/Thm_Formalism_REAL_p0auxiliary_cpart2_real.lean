-- Prove2me | Theorems.Thm_Formalism_REAL_p0auxiliary_cpart2_real
-- name    : Formalism.REAL.p0auxiliary_cpart2_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:58:00.998826+00:00
-- url     : https://prove2.me/theorems/e860be32-2f10-49ac-87c9-c3a7d83ec854
-- title:
--   REAL: p0auxiliary cpart2 real
-- statement:
--   The REAL construction uses the p0auxiliary cpart2 real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LieOperatorConjHolds.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LieOperatorConjHolds.lean#L77-L80

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.p0auxiliary_cpart2_real {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε ((x : ℂ) • Z) = (x : ℂ) • cpart2 ε Z := by sorry
