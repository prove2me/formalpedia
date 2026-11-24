-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_dw_int
-- name    : Formalism.InvariantFactorPaths.L4.dw_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:29.629881+00:00
-- url     : https://prove2.me/theorems/8b34e3ed-c7ad-47e0-8cce-8d637148cb6f
-- title:
--   L4: dw int
-- statement:
--   The L4 construction uses the dw int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L186-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L186-L192

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
variable (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.dw_int (l : List (Fin r × ℕ)) (hl : ∀ ck ∈ l, ck.1 ≠ 0) (b : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hb : b ∈ IntPol p (Fin N × Fin r)) : dw p LL j l b ∈ IntPol p (Fin N × Fin r) := by sorry
