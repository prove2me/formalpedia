-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_u_y
-- name    : Formalism.InvariantFactorPaths.L4.u_y
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:57:09.286566+00:00
-- url     : https://prove2.me/theorems/e26e5b4a-538f-4601-a4e7-29f11b4d4024
-- title:
--   L4: u y
-- statement:
--   The L4 construction uses the u y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L55-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L55-L68

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

theorem Formalism.InvariantFactorPaths.L4.u_y (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (a : Fin (s + 1)) (o : ℕ) :
    ∀ h ∈ Y p (setLast LL o) J M, Uop p LL c univ a h ∈ Y p (setLast LL (o + 1)) J M := by sorry
