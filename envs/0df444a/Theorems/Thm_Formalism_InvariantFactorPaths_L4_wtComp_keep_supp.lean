-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_keep_supp
-- name    : Formalism.InvariantFactorPaths.L4.wtComp_keep_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:49.716808+00:00
-- url     : https://prove2.me/theorems/10223e6a-c6f1-4ab1-9897-bb14be5707f8
-- title:
--   L4: wt Comp keep supp
-- statement:
--   The L4 construction uses the wt Comp keep supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L458-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L458-L469

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

theorem Formalism.InvariantFactorPaths.L4.wtComp_keep_supp (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (Q : Set (Fin N × Fin r →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, wtComp p LL j w x ∈ restrictSupport ℚ_[p] Q := by sorry
