-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X
-- name    : Formalism.InvariantFactorPaths.L4.glAct_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:15.150294+00:00
-- url     : https://prove2.me/theorems/e4712f29-f5cc-4905-9bc1-faf200794c7e
-- title:
--   L4: gl Act X
-- statement:
--   The L4 construction uses the gl Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L147-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L147-L165

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

theorem Formalism.InvariantFactorPaths.L4.glAct_X (LL : Letters N) (j : ℕ) (a b c : Fin r) (i : Fin N) :
    glAct p LL j a b (X (i, c)) =
      if (i : ℕ) < j then (if LL.vec i then (if b = c then X (i, a) else 0) else (if a = c then -X (i, b) else 0))
      else 0 := by sorry
