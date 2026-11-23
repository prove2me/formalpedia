-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_conj_quad
-- name    : Formalism.FourierDecayAlt.P.Jx8.conj_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:03.294882+00:00
-- url     : https://prove2.me/theorems/9122097b-ac24-4f7f-ad38-e753c5803f99
-- title:
--   Jx8: conj quad
-- statement:
--   The Jx8 construction uses the conj quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L99-L107

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

theorem Formalism.FourierDecayAlt.P.Jx8.conj_quad (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) = ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by sorry
