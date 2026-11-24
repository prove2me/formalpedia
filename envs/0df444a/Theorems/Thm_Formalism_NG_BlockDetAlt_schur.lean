-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_schur
-- name    : Formalism.NG.BlockDetAlt.schur
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:51.721499+00:00
-- url     : https://prove2.me/theorems/b06891bf-abdf-4bc4-8659-10fcb356e5e3
-- title:
--   Block Det Alt: schur
-- statement:
--   The Block Det Alt construction uses the schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L307-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L307-L369

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
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]

theorem Formalism.NG.BlockDetAlt.schur (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hyp : HypDet T' R') (g : Type) [Fintype g] : SchurP T' R' g := by sorry
