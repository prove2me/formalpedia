-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_continuousAt
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_character_continuousAt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:55.03789+00:00
-- url     : https://prove2.me/theorems/22d6812b-579f-4c68-8159-e3c1f552aa49
-- title:
--   Zero Free Dirichlet: chebyshev character continuous At
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev character continuous At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L210-L216

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

theorem Formalism.ZeroFreeDirichlet.chebyshev_character_continuousAt (y : ℝ) : ContinuousAt (fun x => Schi χ x) y := by sorry
