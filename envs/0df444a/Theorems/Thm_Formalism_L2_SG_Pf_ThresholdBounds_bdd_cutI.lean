-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_bdd_cutI
-- name    : Formalism.L2.SG.Pf.ThresholdBounds.bdd_cutI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:21.143062+00:00
-- url     : https://prove2.me/theorems/9981a1bd-b16c-4b37-a973-5004a0d64497
-- title:
--   Threshold Bounds: bdd cut I
-- statement:
--   The Threshold Bounds construction uses the bdd cut I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ThresholdBounds.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ThresholdBounds.lean#L180-L185

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

theorem Formalism.L2.SG.Pf.ThresholdBounds.bdd_cutI (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) :
    BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by sorry
