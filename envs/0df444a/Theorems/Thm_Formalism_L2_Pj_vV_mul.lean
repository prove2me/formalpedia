-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vV_mul
-- name    : Formalism.L2.Pj.vV_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:36.352668+00:00
-- url     : https://prove2.me/theorems/59726799-cf58-4e80-bb8a-7922a74a67fb
-- title:
--   Pj: v V mul
-- statement:
--   The Pj construction uses the v V mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
variable {V}

theorem Formalism.L2.Pj.vV_mul {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) : vV V (x * y) = vV V x + vV V y := by sorry
