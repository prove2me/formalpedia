-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_le_ycondC
-- name    : Formalism.InvariantFactorPaths.L4.typesLE_le_ycondC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:52.628843+00:00
-- url     : https://prove2.me/theorems/e190ebf9-5c07-470d-9bcc-0730b12abf76
-- title:
--   L4: types LE le ycond C
-- statement:
--   The L4 construction uses the types LE le ycond C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/TypesLELeYcondC.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/TypesLELeYcondC.lean#L115-L117

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
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

theorem Formalism.InvariantFactorPaths.L4.typesLE_le_ycondC [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) : TypesLE p LL j Cs Mt ≤ YCondC p LL j Cs Mt := by sorry
