-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_ev_small
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.ev_small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:49.326077+00:00
-- url     : https://prove2.me/theorems/f346adb4-aa91-415e-84ab-4f80002a2ff6
-- title:
--   Tail Sums Hook Formula Torsion: ev small
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the ev small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L455-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L455-L472

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.ev_small (p C₁ c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      L ^ p * (C₁ * (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)))) ≤ 1 / 6 := by sorry
