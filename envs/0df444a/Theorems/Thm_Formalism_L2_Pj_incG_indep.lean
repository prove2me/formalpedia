-- Prove2me | Theorems.Thm_Formalism_L2_Pj_incG_indep
-- name    : Formalism.L2.Pj.incG_indep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:51.264425+00:00
-- url     : https://prove2.me/theorems/5cec7ad1-1750-4cae-abf3-1d4330cac72e
-- title:
--   Pj: inc G indep
-- statement:
--   The Pj construction uses the inc G indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L34-L48

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

theorem Formalism.L2.Pj.incG_indep (hkey : Function.Injective key) :
    iSupIndep fun w : W => LinearMap.range (incG key C w) := by sorry
