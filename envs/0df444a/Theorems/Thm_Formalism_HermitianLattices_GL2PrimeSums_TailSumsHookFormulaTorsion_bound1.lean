-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_bound1
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.bound1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:40.466557+00:00
-- url     : https://prove2.me/theorems/48c65489-a191-43a4-ad09-47ddfb096c3e
-- title:
--   Tail Sums Hook Formula Torsion: bound1
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the bound1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L382-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L382-L422

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

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.bound1 (x Q : ℝ) (hx : 3 ≤ x) (hQ : 1 ≤ Q) :
    3 ≤ ⌊x ^ (400 : ℝ)⌋₊ ∧ ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 2 / x ∧
      0 ≤ Real.log ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) * Q) ∧
      Real.log ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) * Q) ≤ 400 * Real.log x + Real.log Q := by sorry
