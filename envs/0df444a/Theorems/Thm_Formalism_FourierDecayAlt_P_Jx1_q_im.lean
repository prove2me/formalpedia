-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_q_im
-- name    : Formalism.FourierDecayAlt.P.Jx1.q_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:19.210692+00:00
-- url     : https://prove2.me/theorems/a6c7260d-9891-478d-9824-d0d964850e33
-- title:
--   Jx1: q im
-- statement:
--   The Jx1 construction uses the q im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L254-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L254-L263

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.Jx1.q_im (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by sorry
