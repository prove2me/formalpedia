-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_sat_main
-- name    : Formalism.InvariantFactorPaths.L4.sat_main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:15:27.924818+00:00
-- url     : https://prove2.me/theorems/32aed6e3-fb40-4b9a-be8f-5888eff0b325
-- title:
--   L4: sat main
-- statement:
--   The L4 construction uses the sat main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedSaturationHolds.lean#L49-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedSaturationHolds.lean#L49-L87

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedSaturationHolds
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
variable {p : ℕ} [Fact p.Prime] {K : ℕ}

theorem Formalism.InvariantFactorPaths.L4.sat_main {s : ℕ} (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
    (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (hcd : c < LL.total)
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hx : x ∈ XSp p LL J M (Fin.last s))
    (hxi : x ∈ IntPol p (Fin (K + 1) × Fin (s + 1))) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin (s + 1)) ∧
      initPart (Fin.last K, Fin.last s) 0 h =
        ((p : ℚ_[p]) ^ (2 * ((s + 1).choose 2 * Nat.log p (4 * LL.total + (s + 1) - 1)))) • x := by sorry
