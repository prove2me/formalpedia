-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_const
-- name    : Formalism.NG.BlockDetAlt.phiMat_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:04.999819+00:00
-- url     : https://prove2.me/theorems/f3d052c3-93fc-476d-8429-159d0e3da345
-- title:
--   Block Det Alt: phi Mat const
-- statement:
--   The Block Det Alt construction uses the phi Mat const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L409-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L409-L413

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

theorem Formalism.NG.BlockDetAlt.phiMat_const (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') :
    (PowerSeries.constantCoeff).mapMatrix (phiMat R' Θ) = 1 := by sorry
