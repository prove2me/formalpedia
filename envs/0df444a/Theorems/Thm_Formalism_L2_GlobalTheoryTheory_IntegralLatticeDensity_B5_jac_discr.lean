-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_jac_discr
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:46.107232+00:00
-- url     : https://prove2.me/theorems/e8f718d4-d5ca-44f2-a3a4-d72d1b4d5915
-- title:
--   B5: jac discr
-- statement:
--   The B5 construction uses the jac discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L114-L121

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    discr (AddSubgroup.closure {a, a * z}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta z ^ 24 := by sorry
