-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_eq_one_or_eq_neg_one_of_sq_eq_one
-- name    : Formalism.ZeroFreeDirichlet.eq_one_or_eq_neg_one_of_sq_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:41.120733+00:00
-- url     : https://prove2.me/theorems/15599871-0f4b-48ed-8ac1-63b216e9c478
-- title:
--   Zero Free Dirichlet: eq one or eq neg one of sq eq one
-- statement:
--   The Zero Free Dirichlet construction uses the eq one or eq neg one of sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/Positivity.lean#L90-L94

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

theorem Formalism.ZeroFreeDirichlet.eq_one_or_eq_neg_one_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    {n : ℕ} (hu : IsUnit (n : ZMod q)) : χ n = 1 ∨ χ n = -1 := by sorry
