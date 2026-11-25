-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtSpC_setLast
-- name    : Formalism.InvariantFactorPaths.L4.wtSpC_setLast
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:20.179092+00:00
-- url     : https://prove2.me/theorems/9f52a259-3b85-4e38-9431-d6ffff108db2
-- title:
--   L4: wt Sp C set Last
-- statement:
--   The L4 construction uses the wt Sp C set Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L116-L117

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))

theorem Formalism.InvariantFactorPaths.L4.wtSpC_setLast (o j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    WtSpC p (setLast LL o) j Cs la = WtSpC p LL j Cs la := by sorry
