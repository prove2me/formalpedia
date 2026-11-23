-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_cap_values_bddAbove
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.cap_values_bddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:34.554794+00:00
-- url     : https://prove2.me/theorems/631b2dd8-95c7-4843-a474-8e9f99fe0164
-- title:
--   Odd Level Gain Bounds: cap values bdd Above
-- statement:
--   The Odd Level Gain Bounds construction uses the cap values bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CapLeOddShiftBound.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CapLeOddShiftBound.lean#L11-L16

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.cap_values_bddAbove (d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d)
    (I : Set ℕ) : BddAbove ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) '' I) := by sorry
