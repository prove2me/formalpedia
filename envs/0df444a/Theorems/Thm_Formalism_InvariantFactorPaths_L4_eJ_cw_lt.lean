-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_cw_lt
-- name    : Formalism.InvariantFactorPaths.L4.eJ_cw_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:59:23.565897+00:00
-- url     : https://prove2.me/theorems/e9405c0c-56ce-461f-be48-b8eeecf0a549
-- title:
--   L4: e J cw lt
-- statement:
--   The L4 construction uses the e J cw lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L281-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L281-L289

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
variable (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
  (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th)
include hv hx

theorem Formalism.InvariantFactorPaths.L4.eJ_cw_lt (s t : Fin r) (hs : s ∈ Cs) (ht : t ∈ Cs) (hst : s < t) (γ : Fin r → ℤ) :
    glAct p LL K s t (cw p K γ x) = -(eW p K s t (cw p K (shiftW γ t s) x)) := by sorry
