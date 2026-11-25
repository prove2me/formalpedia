-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_lamData_cfg
-- name    : CompanionTheory.WaveGrid.lamData_cfg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:32.990867+00:00
-- url     : https://prove2.me/theorems/b67d1590-a9a7-541f-8323-32e7110fb2cf
-- title:
--   Wave Grid: lam Data cfg
-- statement:
--   The Wave Grid construction uses the lam Data cfg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L100-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L100-L142

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
variable (c : Sz.Cfg)

theorem CompanionTheory.WaveGrid.lamData_cfg (r : ℕ) (hm : c.m = 2 * r + 2) (hok : c.Ok) (T T' : ℝ) (de de' : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) (hde' : ∀ i, de' i = 0 ∨ de' i = 1) (cs b : ℝ) (hc0 : 0 < cs)
    (hc : 1 + cs ≤ 4 * c.Del) (ha : c.a ≤ b) (hb : ∀ j, 1 ≤ j → j ≤ c.m → c.b j ≤ b) :
    LamData (cfgPar c r T T' de de') c.lam cs (4 * c.Del) b := by sorry
