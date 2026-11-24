-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_surjective
-- name    : Formalism.InvariantFactorPaths.L4.restriction_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:33.897492+00:00
-- url     : https://prove2.me/theorems/52b1cc52-c8ea-469f-a6e8-679d1d856331
-- title:
--   L4: restriction surjective
-- statement:
--   The L4 construction uses the restriction surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L208-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L208-L298

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.restriction_surjective [NeZero r] (hΩ : OmegaInj) (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ (o : ℕ), ∀ x ∈ XSp p (setLast LL o) J M ρ,
      ∃ h ∈ Y p (setLast LL o) J M, resL p (Fin.last K, ρ) 0 h = x := by sorry
