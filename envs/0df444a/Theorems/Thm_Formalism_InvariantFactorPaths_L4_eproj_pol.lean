-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_pol
-- name    : Formalism.InvariantFactorPaths.L4.eproj_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:38.686049+00:00
-- url     : https://prove2.me/theorems/2f80627e-1720-41ec-b8d3-f6809fc45876
-- title:
--   L4: eproj pol
-- statement:
--   The L4 construction uses the eproj pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L276-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L276-L363

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.eproj_pol (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) :
    ∀ F ∈ Pol p r LL, F ∈ WtSpC p LL j univ w → PE F ∈ Pol p r LL := by sorry
