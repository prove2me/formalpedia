-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_fix
-- name    : Formalism.InvariantFactorPaths.L4.ycond_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:24.5528+00:00
-- url     : https://prove2.me/theorems/5d93e64d-55d1-47c5-b8e1-a809fbcb00ce
-- title:
--   L4: ycond fix
-- statement:
--   The L4 construction uses the ycond fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L428-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L428-L435

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.ycond_fix [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ)) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (hT : ∀ la : Fin r → ℤ, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt → la ∈ T) :
    ∀ x ∈ YCond p LL j Mt ⊓ Pol p r LL, P x = x := by sorry
