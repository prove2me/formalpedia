-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_pow_mul_ne
-- name    : Formalism.InvariantFactorPaths.L4.coeff_pow_mul_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:59:18.251201+00:00
-- url     : https://prove2.me/theorems/00c4b0ef-7562-4046-9460-97abf7a906ae
-- title:
--   L4: coeff pow mul ne
-- statement:
--   The L4 construction uses the coeff pow mul ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundOfRestrictionOfProj.lean#L105-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundOfRestrictionOfProj.lean#L105-L119

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
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

theorem Formalism.InvariantFactorPaths.L4.coeff_pow_mul_ne (v : σ) (e : ℕ) (y : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) (m : σ →₀ ℕ)
    (hm : m v ≠ e) : coeff m (X v ^ e * y) = 0 := by sorry
