-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_MC_per_rowX
-- name    : Formalism.InvariantFactorPaths.MC.per_rowX
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:21.277369+00:00
-- url     : https://prove2.me/theorems/bbf89888-7d83-4959-adfc-372a893f3bd8
-- title:
--   MC: per row X
-- statement:
--   The MC construction uses the per row X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/NatLogLeOfLe.lean#L38-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/NatLogLeOfLe.lean#L38-L93

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMXB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_NatLogLeOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC
open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.InvariantFactorPaths.OddLevelGainBounds.TB

theorem Formalism.InvariantFactorPaths.MC.per_rowX (p : ℕ) [hp : Fact p.Prime] (Xb S o z e Mm : ℕ) (κ κ4 lgv : ℝ)
    (heo : e ≤ o) (ho : o ≤ Xb) (hS : S ≤ Xb) (hz : z + o ≤ Xb) (hL : (Nat.log p Xb : ℝ) + 1 ≤ lgv)
    (hκ0 : 0 ≤ κ) (hM : Mm = ⌈κ⌉₊) :
    -Real.logb p ‖betaT p Mm z o S e‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ4 ≤
      κ + 3 * lgv + κ4 := by sorry
