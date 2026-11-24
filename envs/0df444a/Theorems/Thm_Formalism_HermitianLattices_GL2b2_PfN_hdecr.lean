-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_hdecr
-- name    : Formalism.HermitianLattices.GL2b2.PfN.hdecr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:03.007861+00:00
-- url     : https://prove2.me/theorems/31fd1d74-e766-40a5-a2a7-45efb026e4df
-- title:
--   Pf N: hdecr
-- statement:
--   The Pf N construction uses the hdecr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L98-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NoExceptionalOfNoRealZero.lean#L98-L116

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

theorem Formalism.HermitianLattices.GL2b2.PfN.hdecr (σ x x' : ℝ) (hσ : 0 < σ) (hx : 0 < x) (hxx : x < x') :
    x' ^ (-σ) - (x' + 2) ^ (-σ) < x ^ (-σ) - (x + 2) ^ (-σ) := by sorry
