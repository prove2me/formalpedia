-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_eul_pderiv
-- name    : Formalism.InvariantFactorPaths.L4.eul_pderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:24.435535+00:00
-- url     : https://prove2.me/theorems/8aeb374a-425c-4efe-b221-3c329af03837
-- title:
--   L4: eul pderiv
-- statement:
--   The L4 construction uses the eul pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L445-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L445-L460

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

theorem Formalism.InvariantFactorPaths.L4.eul_pderiv (LL : Letters (K + 1)) (o : ℕ) (a : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hP : x ∈ Pol p r (setLast LL (o + 1))) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (pderiv (Fin.last K, a) x) =
      ((o : ℕ) : ℚ_[p]) • pderiv (Fin.last K, a) x := by sorry
