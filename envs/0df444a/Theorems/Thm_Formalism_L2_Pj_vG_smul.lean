-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vG_smul
-- name    : Formalism.L2.Pj.vG_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:17.237113+00:00
-- url     : https://prove2.me/theorems/56f85b1d-d106-4c40-9739-6e3575a8df73
-- title:
--   Pj: v G smul
-- statement:
--   The Pj construction uses the v G smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L100-L106

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
variable {v : R → EReal}

theorem Formalism.L2.Pj.vG_smul {a : K} {t : ℝ} (hs : ∀ r, v (a • r) = (t : EReal) + v r) (x : AddMonoidAlgebra R M) :
    vG v (a • x) = (t : EReal) + vG v x := by sorry
