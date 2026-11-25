-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtot_fd
-- name    : Formalism.InvariantFactorPaths.L4.wtot_fd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:39.320085+00:00
-- url     : https://prove2.me/theorems/2cb3e264-6df5-5198-97bf-74eade84f534
-- title:
--   L4: wtot fd
-- statement:
--   The L4 construction uses the wtot fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L202-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L202-L222

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
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)

theorem Formalism.InvariantFactorPaths.L4.wtot_fd (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) : FiniteDimensional ℚ_[p] (Wtot p LL J M (Fin.last s)) := by sorry
