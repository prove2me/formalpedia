-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx1_psd_pullback
-- name    : Formalism.FourierDecayAlt.P.Cx1.psd_pullback
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:19:32.646623+00:00
-- url     : https://prove2.me/theorems/67ce738a-1b46-4685-9a65-e1de1d81effe
-- title:
--   Cx1: psd pullback
-- statement:
--   The Cx1 construction uses the psd pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelZeroEstimateProduct.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelZeroEstimateProduct.lean#L16-L19

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.Cx1

theorem Formalism.FourierDecayAlt.P.Cx1.psd_pullback {α β : Type} (Y : Finset α) (φ : α → β) (k : β → β → ℂ) (Z : Finset β)
    (hZ : ∀ x ∈ Y, φ x ∈ Z) (h : TB.PSDOn Z k) : TB.PSDOn Y (fun x y => k (φ x) (φ y)) := by sorry
