-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_discr_closure_pair_ne_zero
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_closure_pair_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:27.524952+00:00
-- url     : https://prove2.me/theorems/e801ed34-c71f-4269-96f1-2fecc721a1be
-- title:
--   B5: discr closure pair ne zero
-- statement:
--   The B5 construction uses the discr closure pair ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/NormArea.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/NormArea.lean#L26-L33

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_NormArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_closure_pair_ne_zero (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    discr (AddSubgroup.closure {a, b}) ≠ 0 := by sorry
