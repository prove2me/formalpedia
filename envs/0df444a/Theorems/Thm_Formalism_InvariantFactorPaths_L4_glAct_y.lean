-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_y
-- name    : Formalism.InvariantFactorPaths.L4.glAct_y
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:00:08.302925+00:00
-- url     : https://prove2.me/theorems/9d6770d0-f961-4aba-8581-a243276849b3
-- title:
--   L4: gl Act y
-- statement:
--   The L4 construction uses the gl Act y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L101-L112

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {r : ℕ} [NeZero r]

theorem Formalism.InvariantFactorPaths.L4.glAct_y (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c d : Fin r) :
    ∀ h ∈ Y p LL J M, glAct p LL (K + 1) c d h ∈ Y p LL J M := by sorry
