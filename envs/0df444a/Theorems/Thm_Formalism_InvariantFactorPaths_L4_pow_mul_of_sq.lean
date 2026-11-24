-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_of_sq
-- name    : Formalism.InvariantFactorPaths.L4.pow_mul_of_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:29.888905+00:00
-- url     : https://prove2.me/theorems/2beb89bf-45ca-46d2-9e42-e3a7287e8e24
-- title:
--   L4: pow mul of sq
-- statement:
--   The L4 construction uses the pow mul of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L16-L31

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)

theorem Formalism.InvariantFactorPaths.L4.pow_mul_of_sq (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c (glAct p LL j 0 c x) = 0) (k : ℕ) :
    ((glAct p LL j 0 c) ^ (k + 1)) (x * g) = x * ((glAct p LL j 0 c) ^ (k + 1)) g +
      ((k + 1 : ℕ) : ℚ_[p]) • (glAct p LL j 0 c x * ((glAct p LL j 0 c) ^ k) g) := by sorry
