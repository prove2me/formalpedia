-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_quadM
-- name    : Formalism.FourierDecayAlt.P.Jx6.quadM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:06.60644+00:00
-- url     : https://prove2.me/theorems/f4197752-f171-41dc-8a59-1e87ff334683
-- title:
--   Jx6: quad M
-- statement:
--   The Jx6 construction uses the quad M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L20-L28

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6

theorem Formalism.FourierDecayAlt.P.Jx6.quadM {α : Type} (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by sorry
