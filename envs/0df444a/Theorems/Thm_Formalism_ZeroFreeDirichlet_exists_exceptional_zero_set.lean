-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_exceptional_zero_set
-- name    : Formalism.ZeroFreeDirichlet.exists_exceptional_zero_set
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:46.092644+00:00
-- url     : https://prove2.me/theorems/e68f375e-bb02-42aa-ab0a-79b822f3eae6
-- title:
--   Zero Free Dirichlet: exists exceptional zero set
-- statement:
--   The Zero Free Dirichlet construction uses the exists exceptional zero set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L45-L69

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.exists_exceptional_zero_set (cZ c₁ : ℝ) (hle : c₁ ≤ cZ)
    (hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      InRegion cZ q s → IsLZero χ s →
        χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
        ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : ∃ B : Finset ℝ, ExcZeros c₁ χ B := by sorry
