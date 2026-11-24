-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_integrableOn
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_character_integrableOn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:17.947304+00:00
-- url     : https://prove2.me/theorems/1d9a98d2-2234-44e9-86ea-1ccd305ce64c
-- title:
--   Zero Free Dirichlet: chebyshev character integrable On
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev character integrable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L229-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L229-L234

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

theorem Formalism.ZeroFreeDirichlet.chebyshev_character_integrableOn {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w - 1) • Schi χ x) (Ioi 1) := by sorry
