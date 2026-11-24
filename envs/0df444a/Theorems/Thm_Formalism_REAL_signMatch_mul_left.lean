-- Prove2me | Theorems.Thm_Formalism_REAL_signMatch_mul_left
-- name    : Formalism.REAL.signMatch_mul_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:21.09041+00:00
-- url     : https://prove2.me/theorems/056e98be-30d5-4568-bcb9-a66f1a69c14c
-- title:
--   REAL: sign Match mul left
-- statement:
--   The REAL construction uses the sign Match mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L135-L140

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {M n' : ℕ}

theorem Formalism.REAL.signMatch_mul_left (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) (a : Fin n') :
    ((if sgnv ε ε' i a then 1 else -1 : ℂ) * (if sgnv ε ε' j a then 1 else -1)) =
      ((sgn ε i j : ℝ) : ℂ) := by sorry
