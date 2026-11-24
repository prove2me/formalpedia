-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_re_negLogDeriv_le_of_real_zero
-- name    : Formalism.ZeroFreeDirichlet.re_negLogDeriv_le_of_real_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:19.450009+00:00
-- url     : https://prove2.me/theorems/d0e775c6-4b5c-4ac4-a248-955f18eb1a4b
-- title:
--   Zero Free Dirichlet: re neg Log Deriv le of real zero
-- statement:
--   The Zero Free Dirichlet construction uses the re neg Log Deriv le of real zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TwoRealOf.lean#L31-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TwoRealOf.lean#L31-L73

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TwoRealOf
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

theorem Formalism.ZeroFreeDirichlet.re_negLogDeriv_le_of_real_zero (C : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) (1 / 5) ∧
          DirichletCharacter.LFunction χ ρ = 0))
    (hm1 : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (β σ : ℝ) (hσ : 1 < σ) (hβσ : β < σ) (hβ9 : 9 / 10 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hb : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re ≤
      C * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) -
        ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) :
    (negLD χ (σ : ℂ)).re ≤ C * Real.log ((q : ℝ) * 2) - 1 / (σ - β) := by sorry
