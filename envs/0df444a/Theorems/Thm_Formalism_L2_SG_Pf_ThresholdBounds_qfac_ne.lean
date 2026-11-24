-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_qfac_ne
-- name    : Formalism.L2.SG.Pf.ThresholdBounds.qfac_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:12.635833+00:00
-- url     : https://prove2.me/theorems/9d92f2b2-ee81-4e34-bd12-02bb25079cdc
-- title:
--   Threshold Bounds: qfac ne
-- statement:
--   The Threshold Bounds construction uses the qfac ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ThresholdBounds.lean#L31-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ThresholdBounds.lean#L31-L96

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

theorem Formalism.L2.SG.Pf.ThresholdBounds.qfac_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    {l : ℕ} (hl : l + 1 ≤ c.k) {Y : ℝ} (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) {i : ℕ} (hi1 : 1 ≤ i)
    (hik : i ≤ c.k) : Y + 1 / 2 + c.u de i ≠ 0 := by sorry
