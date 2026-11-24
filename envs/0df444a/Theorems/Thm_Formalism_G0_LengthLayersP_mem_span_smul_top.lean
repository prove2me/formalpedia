-- Prove2me | Theorems.Thm_Formalism_G0_LengthLayersP_mem_span_smul_top
-- name    : Formalism.G0.LengthLayersP.mem_span_smul_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:22.796274+00:00
-- url     : https://prove2.me/theorems/d6c98fdb-c39c-4a85-8a18-50ad155b1597
-- title:
--   Length Layers P: mem span smul top
-- statement:
--   The Length Layers P construction uses the mem span smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean#L62-L65

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
variable {O : Type} [CommRing O]

theorem Formalism.G0.LengthLayersP.mem_span_smul_top {X : Type} [AddCommGroup X] [Module O X] (a : O) (x : X) :
    x ∈ (Ideal.span {a}) • (⊤ : Submodule O X) ↔ ∃ y, a • y = x := by sorry
