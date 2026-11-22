-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_single_add
-- name    : Formalism.InvariantFactorPaths.L4.wt_single_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:10.987064+00:00
-- url     : https://prove2.me/theorems/ccdc7be0-f581-4ea0-8dc5-cff59377abd3
-- title:
--   L4: wt single add
-- statement:
--   The L4 construction uses the wt single add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L173-L176

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

theorem Formalism.InvariantFactorPaths.L4.wt_single_add (LL : Letters N) (j : ℕ) (c' : Fin r) (i : Fin N) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c' (Finsupp.single (i, c) 1 + m) = wt LL j c' m +
      (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (if c = c' then 1 else 0) := by sorry
