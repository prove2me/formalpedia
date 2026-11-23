-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quadM
-- name    : Formalism.FourierDecayAlt.P.Jx8.quadM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:27.506265+00:00
-- url     : https://prove2.me/theorems/65adcbdd-4be3-4817-adb9-dba47ca26018
-- title:
--   Jx8: quad M
-- statement:
--   The Jx8 construction uses the quad M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L89-L97

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

theorem Formalism.FourierDecayAlt.P.Jx8.quadM (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by sorry
