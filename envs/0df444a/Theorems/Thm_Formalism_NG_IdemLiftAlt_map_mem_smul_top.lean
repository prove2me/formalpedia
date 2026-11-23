-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_map_mem_smul_top
-- name    : Formalism.NG.IdemLiftAlt.map_mem_smul_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:22.597269+00:00
-- url     : https://prove2.me/theorems/9cf44841-d3f0-4f8e-9b89-e5cc45924254
-- title:
--   Idem Lift Alt: map mem smul top
-- statement:
--   The Idem Lift Alt construction uses the map mem smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L58-L63

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]

theorem Formalism.NG.IdemLiftAlt.map_mem_smul_top (I : Ideal O) {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : M →ₗ[O] N) {x : M} (hx : x ∈ I • (⊤ : Submodule O M)) :
    φ x ∈ I • (⊤ : Submodule O N) := by sorry
