-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_of_ne
-- name    : Formalism.L2.Pj.nval_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:55.774358+00:00
-- url     : https://prove2.me/theorems/a4bce7ec-0de8-4def-96b8-9a8678979ebf
-- title:
--   Pj: nval of ne
-- statement:
--   The Pj construction uses the nval of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L57-L59

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

theorem Formalism.L2.Pj.nval_of_ne {e : ℕ} {x : K'} (hx : x ≠ 0) :
    nval V e x = (((vV V x : ℝ) / e : ℝ) : EReal) := by sorry
