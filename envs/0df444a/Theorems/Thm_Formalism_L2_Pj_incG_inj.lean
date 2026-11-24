-- Prove2me | Theorems.Thm_Formalism_L2_Pj_incG_inj
-- name    : Formalism.L2.Pj.incG_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:27.519838+00:00
-- url     : https://prove2.me/theorems/4dd57bf2-5b3f-43be-97c6-ff63d9bea6fa
-- title:
--   Pj: inc G inj
-- statement:
--   The Pj construction uses the inc G inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L29-L32

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

theorem Formalism.L2.Pj.incG_inj (w : W) : Function.Injective (incG key C w) := by sorry
