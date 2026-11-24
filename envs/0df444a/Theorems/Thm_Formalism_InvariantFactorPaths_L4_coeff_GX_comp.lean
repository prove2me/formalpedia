-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_GX_comp
-- name    : Formalism.InvariantFactorPaths.L4.coeff_GX_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:09.549807+00:00
-- url     : https://prove2.me/theorems/7e3c7a92-4105-41d6-9e30-65966fa7b3d0
-- title:
--   L4: coeff GX comp
-- statement:
--   The L4 construction uses the coeff GX comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/WmMulWmComm.lean#L414-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/WmMulWmComm.lean#L414-L417

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}

theorem Formalism.InvariantFactorPaths.L4.coeff_GX_comp (LL : Letters (K + 1)) (c : ℤ) (hv : LL.vec (Fin.last K) = true) (μ : Fin (s + 1) → ℤ)
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) :
    coeff m ((GX p LL c hv).comp μ x) = if wtX LL c m = μ then coeff m x else 0 := by sorry
