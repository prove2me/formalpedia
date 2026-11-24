-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_invGood
-- name    : Formalism.NG.BlockDetAlt.invGood
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:07.163169+00:00
-- url     : https://prove2.me/theorems/a164fc48-db4d-4df6-a744-157d2403ca4f
-- title:
--   Block Det Alt: inv Good
-- statement:
--   The Block Det Alt construction uses the inv Good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L252-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L252-L285

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

theorem Formalism.NG.BlockDetAlt.invGood (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    {A : Matrix d d (PowerSeries (X' → FractionRing O))} (hA : A ∈ goodM R')
    (hc : (PowerSeries.constantCoeff).mapMatrix A = 1) : A⁻¹ ∈ goodM R' := by sorry
