-- Prove2me | Theorems.Thm_Formalism_L2_Pj_min_le_vV_add
-- name    : Formalism.L2.Pj.min_le_vV_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:42.210164+00:00
-- url     : https://prove2.me/theorems/34def1f0-6c9b-43ea-85dc-a663692c3e76
-- title:
--   Pj: min le v V add
-- statement:
--   The Pj construction uses the min le v V add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L39-L46

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

theorem Formalism.L2.Pj.min_le_vV_add {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vV V x) (vV V y) ≤ vV V (x + y) := by sorry
