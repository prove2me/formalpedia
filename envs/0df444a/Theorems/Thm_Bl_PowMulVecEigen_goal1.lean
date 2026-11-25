-- Prove2me | Theorems.Thm_Bl_PowMulVecEigen_goal1
-- name    : Bl.PowMulVecEigen.goal1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:11.648681+00:00
-- url     : https://prove2.me/theorems/3b1cb1bb-531c-47ca-aa99-197172f1b772
-- title:
--   Pow Mul Vec Eigen: goal1
-- statement:
--   The Pow Mul Vec Eigen construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PowMulVecEigen/PowMulVecEig.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PowMulVecEigen/PowMulVecEig.lean#L17-L25

import Mathlib
import Definitions.Def_Lemmata_PowMulVecEigen_PowMulVecEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Bl Bl.PowMulVecEigen
variable {C : Type} [Field C]

theorem Bl.PowMulVecEigen.goal1 {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by sorry
