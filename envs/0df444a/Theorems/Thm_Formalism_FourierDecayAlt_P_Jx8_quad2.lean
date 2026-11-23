-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quad2
-- name    : Formalism.FourierDecayAlt.P.Jx8.quad2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:01.842304+00:00
-- url     : https://prove2.me/theorems/81876301-5ed8-46f1-ac9f-1bc9c9497adb
-- title:
--   Jx8: quad2
-- statement:
--   The Jx8 construction uses the quad2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L146-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L146-L166

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.Jx8.quad2 [DecidableEq α] (F : Finset α) (k : α → α → ℂ) (x y : α) (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x ≠ y) (c : ℂ) :
    ∑ u ∈ F, ∑ v ∈ F, (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v =
      k x x + conj c * k x y + c * k y x + c * conj c * k y y := by sorry
