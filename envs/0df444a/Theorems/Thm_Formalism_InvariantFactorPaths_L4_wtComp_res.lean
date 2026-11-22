-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_res
-- name    : Formalism.InvariantFactorPaths.L4.wtComp_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:16.04768+00:00
-- url     : https://prove2.me/theorems/0dfa6f33-4105-48cc-86fe-17faa5abadc8
-- title:
--   L4: wt Comp res
-- statement:
--   The L4 construction uses the wt Comp res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L471-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L471-L481

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

theorem Formalism.InvariantFactorPaths.L4.wtComp_res (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (v : Fin N × Fin r) (e : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (wtComp p LL j w x) = wtComp p LL j w (resL p v e x) := by sorry
