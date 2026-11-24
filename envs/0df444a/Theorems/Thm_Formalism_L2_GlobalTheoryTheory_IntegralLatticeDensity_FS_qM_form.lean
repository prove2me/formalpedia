-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_qM_form
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:59.569592+00:00
-- url     : https://prove2.me/theorems/f95edea1-99e8-4e02-b23c-aa62d0b9b9d8
-- title:
--   FS: q M form
-- statement:
--   The FS construction uses the q M form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L28-L32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_form (p q r s : K) (u v : Fin 4 → K) :
    ∑ β, (∑ a, qM p q r s β a * u a) * (∑ a, qM p q r s β a * v a)
      = (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * ∑ a, u a * v a := by sorry
