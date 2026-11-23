-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_psd_comp
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.psd_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:21.997807+00:00
-- url     : https://prove2.me/theorems/39002a97-9e9d-4174-b2ee-106b149e24b8
-- title:
--   Block Start Points: psd comp
-- statement:
--   The Block Start Points construction uses the psd comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L28-L30

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.psd_comp {α β : Type} (Y : Finset α) (Z : Finset β) (φ : α → β) (hφ : ∀ a ∈ Y, φ a ∈ Z)
    (k : β → β → ℂ) (hk : PSDOn Z k) : PSDOn Y (fun a b => k (φ a) (φ b)) := by sorry
