-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_div_int
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_div_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:42.11387+00:00
-- url     : https://prove2.me/theorems/4a144fef-1d6d-46c4-8f7d-2b2aa48aabee
-- title:
--   L4: pderiv div int
-- statement:
--   The L4 construction uses the pderiv div int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L30-L37

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

theorem Formalism.InvariantFactorPaths.L4.pderiv_div_int (v : σ) (k : ℕ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ IntPol p σ) :
    ((k.factorial : ℚ_[p]))⁻¹ •
      ((((pderiv v).toLinearMap : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) ^ k) x) ∈ IntPol p σ := by sorry
