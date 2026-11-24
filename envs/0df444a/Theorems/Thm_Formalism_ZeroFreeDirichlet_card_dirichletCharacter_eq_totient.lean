-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_card_dirichletCharacter_eq_totient
-- name    : Formalism.ZeroFreeDirichlet.card_dirichletCharacter_eq_totient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:34.011618+00:00
-- url     : https://prove2.me/theorems/b82fb288-dcb3-4f92-a405-f3c03b6afd4d
-- title:
--   Zero Free Dirichlet: card dirichlet Character eq totient
-- statement:
--   The Zero Free Dirichlet construction uses the card dirichlet Character eq totient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszAPOf.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszAPOf.lean#L37-L40

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
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

theorem Formalism.ZeroFreeDirichlet.card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by sorry
