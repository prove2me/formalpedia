-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
-- name    : Formalism.InvariantFactorPaths.L4.glAct_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:51.81163+00:00
-- url     : https://prove2.me/theorems/b98832e6-e5c4-40b9-a37a-25c93d768c1d
-- title:
--   L4: gl Act mul
-- statement:
--   The L4 construction uses the gl Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L140-L145

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

theorem Formalism.InvariantFactorPaths.L4.glAct_mul (LL : Letters N) (j : ℕ) (a b : Fin r) (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j a b (f * g) = glAct p LL j a b f * g + f * glAct p LL j a b g := by sorry
