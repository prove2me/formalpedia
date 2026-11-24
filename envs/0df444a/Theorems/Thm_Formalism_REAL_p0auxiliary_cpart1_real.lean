-- Prove2me | Theorems.Thm_Formalism_REAL_p0auxiliary_cpart1_real
-- name    : Formalism.REAL.p0auxiliary_cpart1_real
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:00.864843+00:00
-- url     : https://prove2.me/theorems/76bb2444-295f-48c7-ad89-6509d832cbc5
-- title:
--   REAL: p0auxiliary cpart1 real
-- statement:
--   The REAL construction uses the p0auxiliary cpart1 real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LieOperatorConjHolds.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LieOperatorConjHolds.lean#L72-L75

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

theorem Formalism.REAL.p0auxiliary_cpart1_real {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε ((x : ℂ) • Z) = (x : ℂ) • cpart1 ε Z := by sorry
