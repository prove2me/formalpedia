-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_glStable
-- name    : Formalism.InvariantFactorPaths.L4.typesLE_glStable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:31.852254+00:00
-- url     : https://prove2.me/theorems/c8ff6b92-3420-4926-b1d4-9a3f58d380c4
-- title:
--   L4: types LE gl Stable
-- statement:
--   The L4 construction uses the types LE gl Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L664-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L664-L669

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
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

theorem Formalism.InvariantFactorPaths.L4.typesLE_glStable {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (M : WithTop ℤ) (s t : Fin r)
    (hs : s ∈ Cs) (ht : t ∈ Cs) : ∀ z ∈ TypesLE p LL j Cs M, glAct p LL j s t z ∈ TypesLE p LL j Cs M := by sorry
