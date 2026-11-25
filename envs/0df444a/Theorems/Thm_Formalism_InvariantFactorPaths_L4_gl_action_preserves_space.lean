-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_gl_action_preserves_space
-- name    : Formalism.InvariantFactorPaths.L4.gl_action_preserves_space
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:02.259825+00:00
-- url     : https://prove2.me/theorems/53ba53f8-5336-57c2-b21e-70f936290f58
-- title:
--   L4: gl action preserves space
-- statement:
--   The L4 construction uses the gl action preserves space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L81-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L81-L93

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
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
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)

theorem Formalism.InvariantFactorPaths.L4.gl_action_preserves_space (i j : Fin s) (o : ℕ) :
    ∀ x ∈ XSp p (setLast LL o) J M (Fin.last s),
      glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j) x ∈ XSp p (setLast LL o) J M (Fin.last s) := by sorry
