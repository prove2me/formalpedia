-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_succ_mul
-- name    : Formalism.InvariantFactorPaths.L4.dpow_succ_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:36.009665+00:00
-- url     : https://prove2.me/theorems/81afb6d2-9bba-4611-98fd-615eb9440fa6
-- title:
--   L4: dpow succ mul
-- statement:
--   The L4 construction uses the dpow succ mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L33-L43

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

theorem Formalism.InvariantFactorPaths.L4.dpow_succ_mul (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c (glAct p LL j 0 c x) = 0) (k : ℕ) :
    dpow p LL j c (k + 1) (x * g) = x * dpow p LL j c (k + 1) g + glAct p LL j 0 c x * dpow p LL j c k g := by sorry
