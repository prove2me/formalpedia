-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_qf_block
-- name    : Formalism.FourierDecayAlt.P.PBA.qf_block
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:48.894007+00:00
-- url     : https://prove2.me/theorems/54811abf-a494-4ef8-abb4-13a734b198bf
-- title:
--   PBA: qf block
-- statement:
--   The PBA construction uses the qf block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L31-L44

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

theorem Formalism.FourierDecayAlt.P.PBA.qf_block (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) (c : α ⊕ β → ℂ) :
    (qf (Y₁.disjSum Y₂) (blockK a w b) c).re =
      (qf Y₁ a (fun p => c (.inl p))).re + (qf Y₂ b (fun q => c (.inr q))).re +
        2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)).re := by sorry
