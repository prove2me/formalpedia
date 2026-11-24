-- Prove2me | Theorems.Thm_Formalism_G0_LengthLayersP_length_span_finset_le
-- name    : Formalism.G0.LengthLayersP.length_span_finset_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:01.730492+00:00
-- url     : https://prove2.me/theorems/5e8dda96-ca0d-40a5-85ef-344f4031272c
-- title:
--   Length Layers P: length span finset le
-- statement:
--   The Length Layers P construction uses the length span finset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L156-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L156-L174

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

theorem Formalism.G0.LengthLayersP.length_span_finset_le (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (D : Finset X) (hD : ∀ x ∈ D, π ^ s • x = 0) :
    Module.length O ↥(Submodule.span O (D : Set X)) ≤ ((D.card * s : ℕ) : ℕ∞) := by sorry
