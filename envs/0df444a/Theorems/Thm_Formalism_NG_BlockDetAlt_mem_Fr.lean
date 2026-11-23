-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_mem_Fr
-- name    : Formalism.NG.BlockDetAlt.mem_Fr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:15.651881+00:00
-- url     : https://prove2.me/theorems/7b62dfb3-5ff0-4eed-9929-a415409d6443
-- title:
--   Block Det Alt: mem Fr
-- statement:
--   The Block Det Alt construction uses the mem Fr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L18-L25

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}

theorem Formalism.NG.BlockDetAlt.mem_Fr {T' : Subalgebra O (X' → O)} {φ : X' → FractionRing O} :
    φ ∈ Fr T' ↔ ∃ f ∈ T', ∀ x', algebraMap O (FractionRing O) (f x') = φ x' := by sorry
