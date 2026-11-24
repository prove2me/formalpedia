-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_term_three_four_one_nonneg
-- name    : Formalism.ZeroFreeDirichlet.term_three_four_one_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:42.973492+00:00
-- url     : https://prove2.me/theorems/85fc0dcd-e991-4832-b906-cc5fd9f1cb04
-- title:
--   Zero Free Dirichlet: term three four one nonneg
-- statement:
--   The Zero Free Dirichlet construction uses the term three four one nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L51-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L51-L88

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

theorem Formalism.ZeroFreeDirichlet.term_three_four_one_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + 4 * (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re
      + (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by sorry
