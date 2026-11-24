-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_vertical_integrable
-- name    : Formalism.ZeroFreeDirichlet.perron_vertical_integrable
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:43:54.134149+00:00
-- url     : https://prove2.me/theorems/fe8c5da7-637b-4141-91d4-cd608b11a14f
-- title:
--   Zero Free Dirichlet: perron vertical integrable
-- statement:
--   The Zero Free Dirichlet construction uses the perron vertical integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L269-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L269-L279

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

theorem Formalism.ZeroFreeDirichlet.perron_vertical_integrable {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => Schi χ x)) (-σ₀) := by sorry
