-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_range_le_ycond
-- name    : Formalism.InvariantFactorPaths.L4.typeProj_range_le_ycond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:36.783834+00:00
-- url     : https://prove2.me/theorems/bb3e4917-770d-4eda-8d6f-63d94c3884aa
-- title:
--   L4: type Proj range le ycond
-- statement:
--   The L4 construction uses the type Proj range le ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L419-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L419-L426

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

theorem Formalism.InvariantFactorPaths.L4.typeProj_range_le_ycond [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ)) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (hT : ∀ la ∈ T, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt) :
    ∀ x, P x ∈ YCond p LL j Mt := by sorry
