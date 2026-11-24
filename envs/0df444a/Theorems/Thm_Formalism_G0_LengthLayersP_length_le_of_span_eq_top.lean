-- Prove2me | Theorems.Thm_Formalism_G0_LengthLayersP_length_le_of_span_eq_top
-- name    : Formalism.G0.LengthLayersP.length_le_of_span_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:57.696806+00:00
-- url     : https://prove2.me/theorems/7edcc3b3-9391-4d59-8008-dd9913344505
-- title:
--   Length Layers P: length le of span eq top
-- statement:
--   The Length Layers P construction uses the length le of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L176-L182

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

theorem Formalism.G0.LengthLayersP.length_le_of_span_eq_top (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (D : Finset X) (hD : ∀ x ∈ D, π ^ s • x = 0)
    (htop : Submodule.span O (D : Set X) = ⊤) :
    Module.length O X ≤ ((D.card * s : ℕ) : ℕ∞) := by sorry
