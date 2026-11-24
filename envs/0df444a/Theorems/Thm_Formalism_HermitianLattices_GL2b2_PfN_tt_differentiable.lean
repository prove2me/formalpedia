-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tt_differentiable
-- name    : Formalism.HermitianLattices.GL2b2.PfN.tt_differentiable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:04:03.472211+00:00
-- url     : https://prove2.me/theorems/f53bc2ca-1211-4193-878a-40036f0d1b82
-- title:
--   Pf N: tt differentiable
-- statement:
--   The Pf N construction uses the tt differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L78-L87

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

theorem Formalism.HermitianLattices.GL2b2.PfN.tt_differentiable (k : ℕ) : Differentiable ℂ (tt k) := by sorry
