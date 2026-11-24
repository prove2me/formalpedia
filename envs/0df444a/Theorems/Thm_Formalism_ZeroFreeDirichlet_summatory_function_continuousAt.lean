-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_function_continuousAt
-- name    : Formalism.ZeroFreeDirichlet.summatory_function_continuousAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:01.327295+00:00
-- url     : https://prove2.me/theorems/6d75cbfe-8778-4bd9-b925-de299e3c95da
-- title:
--   Zero Free Dirichlet: summatory function continuous At
-- statement:
--   The Zero Free Dirichlet construction uses the summatory function continuous At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L199-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L199-L208

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.ZeroFreeDirichlet.summatory_function_continuousAt {a : ℕ → ℝ} (ha0 : a 0 = 0) (y : ℝ) :
    ContinuousAt (fun x => (Formalism.Sa a x : ℂ)) y := by sorry
