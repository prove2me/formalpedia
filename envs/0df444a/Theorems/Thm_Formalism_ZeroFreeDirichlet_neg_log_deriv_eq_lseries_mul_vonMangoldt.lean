-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_eq_lseries_mul_vonMangoldt
-- name    : Formalism.ZeroFreeDirichlet.neg_log_deriv_eq_lseries_mul_vonMangoldt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:30.639897+00:00
-- url     : https://prove2.me/theorems/615a302a-a1b5-4625-9ab5-5f2fd4f46297
-- title:
--   Zero Free Dirichlet: neg log deriv eq lseries mul von Mangoldt
-- statement:
--   The Zero Free Dirichlet construction uses the neg log deriv eq lseries mul von Mangoldt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L83-L91

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.ZeroFreeDirichlet.neg_log_deriv_eq_lseries_mul_vonMangoldt {w : ℂ} (hw : 1 < w.re) : negLD χ w = LSeries (↗χ * ↗Λ) w := by sorry
