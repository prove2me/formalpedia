-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_E6_eq_half_eisensteinSeries
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.E6_eq_half_eisensteinSeries
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:15.375316+00:00
-- url     : https://prove2.me/theorems/5265ae70-a349-410c-baf8-1c98175c4520
-- title:
--   B5: E6 eq half eisenstein Series
-- statement:
--   The B5 construction uses the E6 eq half eisenstein Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L93-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L93-L94

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.E6_eq_half_eisensteinSeries (z : UpperHalfPlane) :
    ModularForm.E₆ z = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (6 : ℕ) z := by sorry
