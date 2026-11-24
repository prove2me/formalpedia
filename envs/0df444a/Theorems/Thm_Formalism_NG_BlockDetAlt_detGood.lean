-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_detGood
-- name    : Formalism.NG.BlockDetAlt.detGood
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:58.006545+00:00
-- url     : https://prove2.me/theorems/294c0cb7-8260-49a8-83cd-9d0f91976bab
-- title:
--   Block Det Alt: det Good
-- statement:
--   The Block Det Alt construction uses the det Good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L220-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L220-L240

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

theorem Formalism.NG.BlockDetAlt.detGood (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hyp : HypDet T' R') {a : Matrix d d (PowerSeries (X' → FractionRing O))}
    (ha : a ∈ goodM R') : a.det ∈ goodS T' := by sorry
