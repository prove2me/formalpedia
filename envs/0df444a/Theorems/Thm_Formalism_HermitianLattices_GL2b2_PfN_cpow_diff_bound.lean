-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_cpow_diff_bound
-- name    : Formalism.HermitianLattices.GL2b2.PfN.cpow_diff_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:48:17.042633+00:00
-- url     : https://prove2.me/theorems/c2441335-ff5a-4fa9-ad18-a41cd7d0de55
-- title:
--   Pf N: cpow diff bound
-- statement:
--   The Pf N construction uses the cpow diff bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L12-L32

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex

theorem Formalism.HermitianLattices.GL2b2.PfN.cpow_diff_bound (s : ℂ) (hs : 0 ≤ s.re) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖((y : ℝ) : ℂ) ^ (-s) - ((x : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) * (y - x) := by sorry
