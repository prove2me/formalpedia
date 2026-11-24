-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_pderiv_pow
-- name    : Formalism.InvariantFactorPaths.L4.coeff_pderiv_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:01.364846+00:00
-- url     : https://prove2.me/theorems/c742ecf9-c7a2-4f65-9773-22ec2871f832
-- title:
--   L4: coeff pderiv pow
-- statement:
--   The L4 construction uses the coeff pderiv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L11-L25

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
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.L4.coeff_pderiv_pow (v : σ) (k : ℕ) (f : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    coeff m ((((pderiv v).toLinearMap : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) ^ k) f) =
      (((m v + k).descFactorial k : ℕ) : ℚ_[p]) * coeff (m + Finsupp.single v k) f := by sorry
