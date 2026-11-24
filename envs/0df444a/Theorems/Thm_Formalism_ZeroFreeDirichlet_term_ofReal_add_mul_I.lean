-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_term_ofReal_add_mul_I
-- name    : Formalism.ZeroFreeDirichlet.term_ofReal_add_mul_I
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:46.521063+00:00
-- url     : https://prove2.me/theorems/1fb74fc7-082c-46df-81cc-41d35d52f472
-- title:
--   Zero Free Dirichlet: term of Real add mul I
-- statement:
--   The Zero Free Dirichlet construction uses the term of Real add mul I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L23-L35

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

theorem Formalism.ZeroFreeDirichlet.term_ofReal_add_mul_I {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ u : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) ((σ : ℂ) + u * I) n =
      ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (χ n / (n : ℂ) ^ ((u : ℂ) * I)) := by sorry
