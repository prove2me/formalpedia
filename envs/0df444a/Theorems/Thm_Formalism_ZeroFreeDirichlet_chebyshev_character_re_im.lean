-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_re_im
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_character_re_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:03.386419+00:00
-- url     : https://prove2.me/theorems/fe42d566-39af-4ba1-be8c-0374ea232462
-- title:
--   Zero Free Dirichlet: chebyshev character re im
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev character re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L43-L50

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

theorem Formalism.ZeroFreeDirichlet.chebyshev_character_re_im (x : ℝ) :
    Schi χ x = (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) := by sorry
