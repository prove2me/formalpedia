-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_trivial_bound
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_character_trivial_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:23.05264+00:00
-- url     : https://prove2.me/theorems/d1cf0a70-f88a-4ffd-b59b-43cb94f6d17d
-- title:
--   Zero Free Dirichlet: chebyshev character trivial bound
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev character trivial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L71-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L71-L105

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

theorem Formalism.ZeroFreeDirichlet.chebyshev_character_trivial_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : 1 ≤ x) :
    ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ x * (Real.log x + 1) := by sorry
