-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_WD
-- name    : Formalism.InvariantFactorPaths.L4.cw_WD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:34.270805+00:00
-- url     : https://prove2.me/theorems/ed37ef5a-2e2b-43b2-b51a-5c260b1facf1
-- title:
--   L4: cw WD
-- statement:
--   The L4 construction uses the cw WD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L143-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L143-L155

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.cw_WD (γ : Fin r → ℤ) (s t : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    cw p K γ (X (Fin.last K, s) * pderiv (Fin.last K, t) x) =
      X (Fin.last K, s) * pderiv (Fin.last K, t) (cw p K (shiftW γ t s) x) := by sorry
