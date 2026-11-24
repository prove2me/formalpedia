-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_pow_one
-- name    : Formalism.InvariantFactorPaths.L4.Uop_pow_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:44.243795+00:00
-- url     : https://prove2.me/theorems/34905a81-4a61-4fde-8107-24b58b13a4fa
-- title:
--   L4: Uop pow one
-- statement:
--   The L4 construction uses the Uop pow one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L243-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L243-L262

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)

theorem Formalism.InvariantFactorPaths.L4.Uop_pow_one (c : ℤ) (k : ℕ) :
    ((Uop p LL c Cs a) ^ k) 1 =
      (((k.factorial : ℤ) * Ring.choose c k : ℤ) : ℚ_[p]) • (X (Fin.last K, a) ^ k) := by sorry
