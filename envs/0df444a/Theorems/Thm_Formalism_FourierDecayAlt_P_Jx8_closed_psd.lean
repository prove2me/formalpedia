-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_closed_psd
-- name    : Formalism.FourierDecayAlt.P.Jx8.closed_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:18.705936+00:00
-- url     : https://prove2.me/theorems/fc05b84a-1eb0-448d-859f-07038ae13a0a
-- title:
--   Jx8: closed psd
-- statement:
--   The Jx8 construction uses the closed psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L258-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L258-L265

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

theorem Formalism.FourierDecayAlt.P.Jx8.closed_psd {X : Type} [TopologicalSpace X] (F : Finset α) (g : X → α → α → ℂ)
    (hg : ∀ x y, Continuous fun T => g T x y) : IsClosed {T | TB.PSDOn F (g T)} := by sorry
