-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_mult_re_one_div_sub_zeros_nonneg
-- name    : Formalism.ZeroFreeDirichlet.sum_mult_re_one_div_sub_zeros_nonneg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:32.099466+00:00
-- url     : https://prove2.me/theorems/a30711ae-d36a-4fc0-bb9c-4fb516a6fd0b
-- title:
--   Zero Free Dirichlet: sum mult re one div sub zeros nonneg
-- statement:
--   The Zero Free Dirichlet construction uses the sum mult re one div sub zeros nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/NoZeroComplexOf.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/NoZeroComplexOf.lean#L22-L26

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_NoZeroComplexOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.sum_mult_re_one_div_sub_zeros_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re := by sorry
