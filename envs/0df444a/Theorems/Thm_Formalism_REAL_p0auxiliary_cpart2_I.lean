-- Prove2me | Theorems.Thm_Formalism_REAL_p0auxiliary_cpart2_I
-- name    : Formalism.REAL.p0auxiliary_cpart2_I
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:57:08.763236+00:00
-- url     : https://prove2.me/theorems/5463fc25-0afa-449a-a9ba-0b88252a1e39
-- title:
--   REAL: p0auxiliary cpart2 I
-- statement:
--   The REAL construction uses the p0auxiliary cpart2 I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LieOperatorConjHolds.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LieOperatorConjHolds.lean#L100-L108

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

theorem Formalism.REAL.p0auxiliary_cpart2_I {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Complex.I • Z) = cpart1 ε Z := by sorry
