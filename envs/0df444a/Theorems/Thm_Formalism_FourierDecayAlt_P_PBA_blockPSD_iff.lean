-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_iff
-- name    : Formalism.FourierDecayAlt.P.PBA.blockPSD_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:13:32.678825+00:00
-- url     : https://prove2.me/theorems/40f6d939-c176-45d8-ab61-e1d9c4b791ea
-- title:
--   PBA: block PSD iff
-- statement:
--   The PBA construction uses the block PSD iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L26-L29

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
variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)

theorem Formalism.FourierDecayAlt.P.PBA.blockPSD_iff (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) :
    KB.BlockPSD Y₁ Y₂ a w b ↔ TB.PSDOn (Y₁.disjSum Y₂) (blockK a w b) := by sorry
