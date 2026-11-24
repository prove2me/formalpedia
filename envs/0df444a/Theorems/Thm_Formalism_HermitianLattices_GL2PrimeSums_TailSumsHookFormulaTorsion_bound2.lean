-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_bound2
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.bound2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:11.556216+00:00
-- url     : https://prove2.me/theorems/d05216cf-2ef7-4fbf-8735-c25b7d742e1a
-- title:
--   Tail Sums Hook Formula Torsion: bound2
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the bound2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L424-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L424-L453

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

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.bound2 (L : ℝ) (hL : 3 ≤ L) :
    3 ≤ ⌈L ^ 800⌉₊ ∧ ((⌈L ^ 800⌉₊ : ℕ) : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 1 / L ^ 2 ∧
      Real.log ((⌈L ^ 800⌉₊ : ℕ) : ℝ) ≤ 1 + 800 * Real.log L := by sorry
