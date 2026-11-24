-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_AdjugateJacobi_mulVec_adjugate_col
-- name    : Formalism.ResultantValuation.AdjugateJacobi.mulVec_adjugate_col
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:32.844993+00:00
-- url     : https://prove2.me/theorems/9e47e0bb-f424-418e-bf36-7799b3e8e905
-- title:
--   Adjugate Jacobi: mul Vec adjugate col
-- statement:
--   The Adjugate Jacobi construction uses the mul Vec adjugate col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Adjugate.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Adjugate.lean#L58-L63

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.AdjugateJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.ResultantValuation.AdjugateJacobi.mulVec_adjugate_col (M : Matrix n n R) (l : n) :
    M *ᵥ (fun r => M.adjugate r l) = M.det • Pi.single l 1 := by sorry
