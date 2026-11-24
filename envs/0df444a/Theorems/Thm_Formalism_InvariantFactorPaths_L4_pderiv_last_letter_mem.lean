-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_last_letter_mem
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_last_letter_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:32.428798+00:00
-- url     : https://prove2.me/theorems/44e54dfc-ebfa-4977-a9ff-e7b047c6295c
-- title:
--   L4: pderiv last letter mem
-- statement:
--   The L4 construction uses the pderiv last letter mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L111-L127

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

theorem Formalism.InvariantFactorPaths.L4.pderiv_last_letter_mem [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ a : Fin r)
    (o : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P)
    (ha : a ≠ ρ) :
    ∀ x ∈ XSp p (setLast LL (o + 1)) J M ρ, pderiv (Fin.last K, a) x ∈ XSp p (setLast LL o) J M ρ := by sorry
