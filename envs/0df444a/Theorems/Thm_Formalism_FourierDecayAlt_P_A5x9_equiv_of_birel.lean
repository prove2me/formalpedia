-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_equiv_of_birel
-- name    : Formalism.FourierDecayAlt.P.A5x9.equiv_of_birel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:46.917537+00:00
-- url     : https://prove2.me/theorems/6a687ebd-806d-42ca-9546-ab81887eef9f
-- title:
--   A5x9: equiv of birel
-- statement:
--   The A5x9 construction uses the equiv of birel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L206-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L206-L221

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

theorem Formalism.FourierDecayAlt.P.A5x9.equiv_of_birel {α β : Type} (A : α → Prop) (B : β → Prop) (C : β → α → Prop)
    (c1 : ∀ a, A a → ∃ b, B b ∧ C b a) (c2 : ∀ b, B b → ∃ a, A a ∧ C b a)
    (c3 : ∀ b a₁ a₂, C b a₁ → C b a₂ → a₁ = a₂)
    (c4 : ∀ a b₁ b₂, B b₁ → B b₂ → C b₁ a → C b₂ a → b₁ = b₂) :
    Nonempty ({a // A a} ≃ {b // B b}) := by sorry
