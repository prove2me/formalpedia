-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_ok_congr
-- name    : Formalism.FourierDecayAlt.P.Jx8.ok_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:36.102813+00:00
-- url     : https://prove2.me/theorems/09407053-d679-40a5-a35f-b9d478fd023a
-- title:
--   Jx8: ok congr
-- statement:
--   The Jx8 construction uses the ok congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L276-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L276-L289

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

theorem Formalism.FourierDecayAlt.P.Jx8.ok_congr {E α : Type} [Field E] {N : E → E → α → α → ℂ} {B : α → α → ℂ} {L L' : AddSubgroup E}
    {Th Th' : E → α → α → ℂ} {F : Finset α}
    (h : ∀ t, ∀ x ∈ F, ∀ y ∈ F, Th t x y = Th' t x y) (hS : (LocSys.mk N Th B L L').Ok F) :
    (LocSys.mk N Th' B L L').Ok F := by sorry
