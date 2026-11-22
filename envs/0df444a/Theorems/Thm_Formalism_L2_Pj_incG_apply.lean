-- Prove2me | Theorems.Thm_Formalism_L2_Pj_incG_apply
-- name    : Formalism.L2.Pj.incG_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:44.376817+00:00
-- url     : https://prove2.me/theorems/e8c4c289-dfda-45db-898b-f575e2653e63
-- title:
--   Pj: inc G apply
-- statement:
--   The Pj construction uses the inc G apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L17-L17

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

theorem Formalism.L2.Pj.incG_apply (w : W) (F : C w) : incG key C w F = AddMonoidAlgebra.single (key w) (F : R) := by sorry
