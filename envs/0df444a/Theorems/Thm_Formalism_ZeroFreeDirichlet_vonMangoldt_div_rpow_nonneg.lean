-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldt_div_rpow_nonneg
-- name    : Formalism.ZeroFreeDirichlet.vonMangoldt_div_rpow_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:33.293792+00:00
-- url     : https://prove2.me/theorems/54357dd6-47ea-4374-8dfb-034fb720797c
-- title:
--   Zero Free Dirichlet: von Mangoldt div rpow nonneg
-- statement:
--   The Zero Free Dirichlet construction uses the von Mangoldt div rpow nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L48-L49

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.vonMangoldt_div_rpow_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ Λ n / (n : ℝ) ^ σ := by sorry
