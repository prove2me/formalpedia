-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_summable_u
-- name    : Formalism.HermitianLattices.GL2b2.PfN.summable_u
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:47:46.268234+00:00
-- url     : https://prove2.me/theorems/4f16fed3-cb69-4772-bd65-f87de29fb2a7
-- title:
--   Pf N: summable u
-- statement:
--   The Pf N construction uses the summable u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L72-L76

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

theorem Formalism.HermitianLattices.GL2b2.PfN.summable_u (δ R : ℝ) (hδ : 0 < δ) :
    Summable (fun k : ℕ => 4 * R * ((k : ℝ) + 1) ^ (-1 - δ)) := by sorry
