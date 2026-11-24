-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_term_one_add_real_nonneg
-- name    : Formalism.ZeroFreeDirichlet.term_one_add_real_nonneg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:52.960804+00:00
-- url     : https://prove2.me/theorems/c1409971-e708-4d2f-a354-9a019c806114
-- title:
--   Zero Free Dirichlet: term one add real nonneg
-- statement:
--   The Zero Free Dirichlet construction uses the term one add real nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L96-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L96-L109

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

theorem Formalism.ZeroFreeDirichlet.term_one_add_real_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ * ↗Λ) (σ : ℂ) n).re := by sorry
