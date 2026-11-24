-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_le_ycondC
-- name    : Formalism.InvariantFactorPaths.L4.isoC_le_ycondC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:06.050904+00:00
-- url     : https://prove2.me/theorems/1de62162-03d2-40d3-b8be-3c6fcc2a133f
-- title:
--   L4: iso C le ycond C
-- statement:
--   The L4 construction uses the iso C le ycond C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/TypesLELeYcondC.lean#L45-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/TypesLELeYcondC.lean#L45-L113

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

theorem Formalism.InvariantFactorPaths.L4.isoC_le_ycondC [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (la : Fin r → ℤ) (Mt : WithTop ℤ) (hla : ((la 0 : ℤ) : WithTop ℤ) ≤ Mt) :
    IsoC p LL j Cs la ≤ YCondC p LL j Cs Mt := by sorry
