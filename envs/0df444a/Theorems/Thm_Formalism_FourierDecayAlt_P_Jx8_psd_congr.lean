-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr
-- name    : Formalism.FourierDecayAlt.P.Jx8.psd_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:28.015817+00:00
-- url     : https://prove2.me/theorems/71f1f574-ed2e-46df-8895-abb9ce537e08
-- title:
--   Jx8: psd congr
-- statement:
--   The Jx8 construction uses the psd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L11-L16

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
variable {α : Type} {F : Finset α}

theorem Formalism.FourierDecayAlt.P.Jx8.psd_congr {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : TB.PSDOn F k) :
    TB.PSDOn F k' := by sorry
