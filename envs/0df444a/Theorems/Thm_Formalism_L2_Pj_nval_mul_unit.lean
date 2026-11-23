-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_mul_unit
-- name    : Formalism.L2.Pj.nval_mul_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:34.503746+00:00
-- url     : https://prove2.me/theorems/32a4e22e-8237-48f6-89ee-90beefad75af
-- title:
--   Pj: nval mul unit
-- statement:
--   The Pj construction uses the nval mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L86-L88

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
variable (V)
variable {V}

theorem Formalism.L2.Pj.nval_mul_unit (e : ℕ) {u : K'} (hu : u ≠ 0) (hu0 : vV V u = 0) (x : K') :
    nval V e (u * x) = nval V e x := by sorry
