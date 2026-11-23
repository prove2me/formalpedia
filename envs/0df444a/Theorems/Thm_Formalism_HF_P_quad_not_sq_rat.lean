-- Prove2me | Theorems.Thm_Formalism_HF_P_quad_not_sq_rat
-- name    : Formalism.HF.P.quad_not_sq_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:35.182458+00:00
-- url     : https://prove2.me/theorems/aad78462-4368-4f03-8248-252358d2602e
-- title:
--   P: quad not sq rat
-- statement:
--   The P construction uses the quad not sq rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/QuadDiscr.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/QuadDiscr.lean#L10-L15

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial Matrix
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.quad_not_sq_rat (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by sorry
