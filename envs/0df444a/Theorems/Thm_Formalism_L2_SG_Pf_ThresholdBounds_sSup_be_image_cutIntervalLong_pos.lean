-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_sSup_be_image_cutIntervalLong_pos
-- name    : Formalism.L2.SG.Pf.ThresholdBounds.sSup_be_image_cutIntervalLong_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:51.70098+00:00
-- url     : https://prove2.me/theorems/25951496-a8a6-4bb4-a8e1-b346655ba3a8
-- title:
--   Threshold Bounds: s Sup be image cut Interval Long pos
-- statement:
--   The Threshold Bounds construction uses the s Sup be image cut Interval Long pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ThresholdBounds.lean#L214-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ThresholdBounds.lean#L214-L226

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)

theorem Formalism.L2.SG.Pf.ThresholdBounds.sSup_be_image_cutIntervalLong_pos (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {N : ℝ} (hN1 : 11 / 4 ≤ N ^ 3)
    (hN2 : N ^ 3 ≤ c.Del / 2) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') {l : ℕ}
    (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm) :
    0 < sSup ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutIntervalLong l N) := by sorry
