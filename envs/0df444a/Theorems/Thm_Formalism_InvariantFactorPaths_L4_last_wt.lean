-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_wt
-- name    : Formalism.InvariantFactorPaths.L4.last_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:47.334152+00:00
-- url     : https://prove2.me/theorems/51082152-9fc6-411c-885d-e3a598c72809
-- title:
--   L4: last wt
-- statement:
--   The L4 construction uses the last wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L296-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L296-L300

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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.last_wt (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt LL j 0 (Finsupp.single (Fin.last K, c) 1 + m) = wt LL j 0 m + (if c = 0 then 1 else 0) := by sorry
