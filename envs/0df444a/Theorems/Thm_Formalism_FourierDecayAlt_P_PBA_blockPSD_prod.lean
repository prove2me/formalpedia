-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_prod
-- name    : Formalism.FourierDecayAlt.P.PBA.blockPSD_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:20.78188+00:00
-- url     : https://prove2.me/theorems/a271ee3b-19c9-451e-9890-7c4e79327db4
-- title:
--   PBA: block PSD prod
-- statement:
--   The PBA construction uses the block PSD prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L168-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L168-L179

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

theorem Formalism.FourierDecayAlt.P.PBA.blockPSD_prod {α β ι : Type} {Y₁ : Finset α} {Y₂ : Finset β} (s : Finset ι) (a : ι → α → α → ℂ)
    (w : ι → α → β → ℂ) (b : ι → β → β → ℂ) (h : ∀ v ∈ s, KB.BlockPSD Y₁ Y₂ (a v) (w v) (b v)) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ∏ v ∈ s, a v p q) (fun p q => ∏ v ∈ s, w v p q)
      (fun p q => ∏ v ∈ s, b v p q) := by sorry
