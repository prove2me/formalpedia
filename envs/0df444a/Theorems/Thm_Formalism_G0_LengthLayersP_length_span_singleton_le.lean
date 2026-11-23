-- Prove2me | Theorems.Thm_Formalism_G0_LengthLayersP_length_span_singleton_le
-- name    : Formalism.G0.LengthLayersP.length_span_singleton_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:56.056026+00:00
-- url     : https://prove2.me/theorems/49f96a8a-c8f2-4fb1-b1d0-e7d4d577ebda
-- title:
--   Length Layers P: length span singleton le
-- statement:
--   The Length Layers P construction uses the length span singleton le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L148-L154

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.G0.LengthLayersP.length_span_singleton_le (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (x : X), π ^ s • x = 0 → Module.length O ↥(O ∙ x) ≤ s := by sorry
