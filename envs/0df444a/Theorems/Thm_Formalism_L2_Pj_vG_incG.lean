-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vG_incG
-- name    : Formalism.L2.Pj.vG_incG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:55.903922+00:00
-- url     : https://prove2.me/theorems/9723f90a-9781-47eb-932c-16d518904bbc
-- title:
--   Pj: v G inc G
-- statement:
--   The Pj construction uses the v G inc G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L70-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L70-L70

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

theorem Formalism.L2.Pj.vG_incG (h0 : v 0 = ⊤) (w : W) (F : C w) : vG v (incG key C w F) = v F := by sorry
