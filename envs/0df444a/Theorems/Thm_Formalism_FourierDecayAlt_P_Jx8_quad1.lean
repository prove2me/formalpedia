-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quad1
-- name    : Formalism.FourierDecayAlt.P.Jx8.quad1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:56.587603+00:00
-- url     : https://prove2.me/theorems/ae6a2bc3-0bef-459d-ade5-37b9cfdf9347
-- title:
--   Jx8: quad1
-- statement:
--   The Jx8 construction uses the quad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L140-L144

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

theorem Formalism.FourierDecayAlt.P.Jx8.quad1 [DecidableEq α] (F : Finset α) (k : α → α → ℂ) (x : α) (hx : x ∈ F) :
    ∑ u ∈ F, ∑ v ∈ F, (if u = x then (1 : ℂ) else 0) * conj (if v = x then (1 : ℂ) else 0) * k u v = k x x := by sorry
