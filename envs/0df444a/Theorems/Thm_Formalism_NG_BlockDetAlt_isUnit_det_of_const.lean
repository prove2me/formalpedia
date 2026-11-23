-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_isUnit_det_of_const
-- name    : Formalism.NG.BlockDetAlt.isUnit_det_of_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:56.580572+00:00
-- url     : https://prove2.me/theorems/c0be3277-3d1b-48c1-9d37-a6f2df93aab1
-- title:
--   Block Det Alt: is Unit det of const
-- statement:
--   The Block Det Alt construction uses the is Unit det of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L246-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L246-L250

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

theorem Formalism.NG.BlockDetAlt.isUnit_det_of_const {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (PowerSeries (X' → FractionRing O)))
    (hA : (PowerSeries.constantCoeff).mapMatrix A = 1) : IsUnit A.det := by sorry
