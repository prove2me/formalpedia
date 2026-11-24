-- Prove2me | Theorems.Thm_Formalism_REAL_re_inner_self_eq_norm_sq
-- name    : Formalism.REAL.re_inner_self_eq_norm_sq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:36.567796+00:00
-- url     : https://prove2.me/theorems/bfe631a2-83f6-40b9-94f6-5a01f2b269dd
-- title:
--   REAL: re inner self eq norm sq
-- statement:
--   The REAL construction uses the re inner self eq norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L409-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L409-L413

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.re_inner_self_eq_norm_sq {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (x : W) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by sorry
