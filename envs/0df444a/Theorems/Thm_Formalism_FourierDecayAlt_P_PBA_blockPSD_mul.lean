-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_mul
-- name    : Formalism.FourierDecayAlt.P.PBA.blockPSD_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:40.732265+00:00
-- url     : https://prove2.me/theorems/cab978d1-d706-497f-870e-d1a5b00d24b4
-- title:
--   PBA: block PSD mul
-- statement:
--   The PBA construction uses the block PSD mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L146-L152

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

theorem Formalism.FourierDecayAlt.P.PBA.blockPSD_mul {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a a' : α → α → ℂ} {w w' : α → β → ℂ}
    {b b' : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) (h' : KB.BlockPSD Y₁ Y₂ a' w' b') :
    KB.BlockPSD Y₁ Y₂ (fun p q => a p q * a' p q) (fun p q => w p q * w' p q) (fun p q => b p q * b' p q) := by sorry
