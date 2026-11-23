-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_raise_nil
-- name    : Formalism.InvariantFactorPaths.L4.raise_nil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:41.791559+00:00
-- url     : https://prove2.me/theorems/55fe6f53-194e-4965-8b90-8950d7963345
-- title:
--   L4: raise nil
-- statement:
--   The L4 construction uses the raise nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L208-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L208-L254

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.raise_nil [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (hc : c ≠ 0)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : ∃ n : ℕ, ((glAct p LL j 0 c) ^ n) h = 0 := by sorry
