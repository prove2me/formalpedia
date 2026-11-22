-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_glStableC
-- name    : Formalism.InvariantFactorPaths.L4.isoC_glStableC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:31.371333+00:00
-- url     : https://prove2.me/theorems/6db25154-54cc-4b80-b348-2530602269a3
-- title:
--   L4: iso C gl Stable C
-- statement:
--   The L4 construction uses the iso C gl Stable C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L45-L51

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

theorem Formalism.InvariantFactorPaths.L4.isoC_glStableC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) (c : Fin r) (hc : c ∈ Cs)
    (d : Fin r) (hd : d ∈ Cs) :
    ∀ x ∈ IsoC p LL j Cs la, glAct p LL j c d x ∈ IsoC p LL j Cs la := by sorry
