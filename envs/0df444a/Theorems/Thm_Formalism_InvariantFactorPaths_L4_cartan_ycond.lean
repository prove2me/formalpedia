-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_cartan_ycond
-- name    : Formalism.InvariantFactorPaths.L4.cartan_ycond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:15.935932+00:00
-- url     : https://prove2.me/theorems/798f8459-64bc-4bd1-9327-d1e167e44aba
-- title:
--   L4: cartan ycond
-- statement:
--   The L4 construction uses the cartan ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L483-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L483-L494

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

theorem Formalism.InvariantFactorPaths.L4.cartan_ycond [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j' Mt, glAct p LL j c c x ∈ YCond p LL j' Mt := by sorry
