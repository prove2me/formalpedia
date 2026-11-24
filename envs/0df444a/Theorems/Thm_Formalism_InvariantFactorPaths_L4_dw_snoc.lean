-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_dw_snoc
-- name    : Formalism.InvariantFactorPaths.L4.dw_snoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:17.912141+00:00
-- url     : https://prove2.me/theorems/ae597909-9c41-4ad2-878f-ee2a67440354
-- title:
--   L4: dw snoc
-- statement:
--   The L4 construction uses the dw snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L128-L131

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

theorem Formalism.InvariantFactorPaths.L4.dw_snoc (ck : Fin r × ℕ) (l : List (Fin r × ℕ)) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    dw p LL j (l ++ [ck]) F = dw p LL j l (dpow p LL j ck.1 ck.2 F) := by sorry
