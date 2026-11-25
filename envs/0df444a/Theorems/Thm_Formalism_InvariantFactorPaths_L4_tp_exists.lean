-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_tp_exists
-- name    : Formalism.InvariantFactorPaths.L4.tp_exists
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:07:35.861423+00:00
-- url     : https://prove2.me/theorems/e3127727-ddb2-48c1-b848-7ff9d257efbe
-- title:
--   L4: tp exists
-- statement:
--   The L4 construction uses the tp exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L36-L43

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}

theorem Formalism.InvariantFactorPaths.L4.tp_exists (LL : Letters (K + 1)) (hs : 1 ≤ s) (Mt : WithTop ℤ) :
    ∃ P, IsTypeProj p LL (K + 1) (univ.erase (Fin.last s)) {la : Fin (s + 1) → ℤ | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P := by sorry
