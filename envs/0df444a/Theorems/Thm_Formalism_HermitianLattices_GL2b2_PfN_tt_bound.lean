-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tt_bound
-- name    : Formalism.HermitianLattices.GL2b2.PfN.tt_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:03:39.30283+00:00
-- url     : https://prove2.me/theorems/f4589055-2b0e-48c0-84aa-0dfefa01d2f9
-- title:
--   Pf N: tt bound
-- statement:
--   The Pf N construction uses the tt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L42-L70

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

theorem Formalism.HermitianLattices.GL2b2.PfN.tt_bound (k : ℕ) (s : ℂ) (δ R : ℝ) (hδ : 0 < δ) (h1 : δ ≤ s.re) (h2 : ‖s‖ ≤ R) :
    ‖tt k s‖ ≤ 4 * R * ((k : ℝ) + 1) ^ (-1 - δ) := by sorry
