-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_off
-- name    : Formalism.FourierDecayAlt.P.Jx8.psd_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:28.517929+00:00
-- url     : https://prove2.me/theorems/385a69a2-6d87-4729-81d8-83dde4771d8b
-- title:
--   Jx8: psd off
-- statement:
--   The Jx8 construction uses the psd off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L229-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L229-L253

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

theorem Formalism.FourierDecayAlt.P.Jx8.psd_off {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) {x y : α} (hx : x ∈ F) (hy : y ∈ F) :
    ‖k x y‖ ≤ (k x x).re + (k y y).re := by sorry
