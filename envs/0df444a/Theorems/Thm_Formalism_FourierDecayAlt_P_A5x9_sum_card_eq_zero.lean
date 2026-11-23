-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_sum_card_eq_zero
-- name    : Formalism.FourierDecayAlt.P.A5x9.sum_card_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:33.86405+00:00
-- url     : https://prove2.me/theorems/a8ced2e2-f31d-4837-97ef-cb1b9fa24944
-- title:
--   A5x9: sum card eq zero
-- statement:
--   The A5x9 construction uses the sum card eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L244-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L244-L268

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Classical

theorem Formalism.FourierDecayAlt.P.A5x9.sum_card_eq_zero {α X : Type} (F : Finset α) (Φ : α → ℂ) (rel : X → α → Prop)
    (hfin : ∀ q ∈ F, Finite {x // rel x q})
    (h0 : ∀ x, ∑ q ∈ F.filter (fun q => rel x q), Φ q = 0) :
    ∑ q ∈ F, (Nat.card {x // rel x q} : ℂ) * Φ q = 0 := by sorry
