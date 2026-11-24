-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_block_cross_le
-- name    : Formalism.FourierDecayAlt.P.PBA.block_cross_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:18.317549+00:00
-- url     : https://prove2.me/theorems/e0936d71-1efe-43a3-a8a2-f2cecafe9afb
-- title:
--   PBA: block cross le
-- statement:
--   The PBA construction uses the block cross le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L181-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L181-L233

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.PBA.block_cross_le {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a : α → α → ℂ} {w : α → β → ℂ}
    {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) :
    ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q‖ ≤ ((∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re + (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re) / 2 := by sorry
