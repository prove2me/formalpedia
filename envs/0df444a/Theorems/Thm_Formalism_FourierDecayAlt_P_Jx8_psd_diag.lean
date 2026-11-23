-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_diag
-- name    : Formalism.FourierDecayAlt.P.Jx8.psd_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:00.041327+00:00
-- url     : https://prove2.me/theorems/a725a443-0cfa-4f72-9e32-8187621f1f50
-- title:
--   Jx8: psd diag
-- statement:
--   The Jx8 construction uses the psd diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L220-L227

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

theorem Formalism.FourierDecayAlt.P.Jx8.psd_diag {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) {x : α} (hx : x ∈ F) :
    (k x x).im = 0 ∧ 0 ≤ (k x x).re := by sorry
