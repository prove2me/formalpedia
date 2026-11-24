-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_good
-- name    : Formalism.NG.BlockDetAlt.phiMat_good
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:58.063082+00:00
-- url     : https://prove2.me/theorems/a364aeb4-85bb-4b1a-b7c4-61f4f6487263
-- title:
--   Block Det Alt: phi Mat good
-- statement:
--   The Block Det Alt construction uses the phi Mat good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L395-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L395-L407

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

theorem Formalism.NG.BlockDetAlt.phiMat_good (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') (p q : g) :
    (Matrix.of fun i j => phiMat R' Θ (p, i) (q, j)) ∈ goodM R' := by sorry
