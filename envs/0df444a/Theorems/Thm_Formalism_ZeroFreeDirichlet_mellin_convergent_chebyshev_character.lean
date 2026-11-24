-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_mellin_convergent_chebyshev_character
-- name    : Formalism.ZeroFreeDirichlet.mellin_convergent_chebyshev_character
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:43:13.014018+00:00
-- url     : https://prove2.me/theorems/6a6db57e-d598-4f11-a8a5-3c34313d11b2
-- title:
--   Zero Free Dirichlet: mellin convergent chebyshev character
-- statement:
--   The Zero Free Dirichlet construction uses the mellin convergent chebyshev character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L258-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L258-L267

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

theorem Formalism.ZeroFreeDirichlet.mellin_convergent_chebyshev_character {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => Schi χ x) ((-σ₀ : ℝ) : ℂ) := by sorry
