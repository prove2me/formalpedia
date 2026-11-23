-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_eq_zero_of_le_one
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_character_eq_zero_of_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:37.672061+00:00
-- url     : https://prove2.me/theorems/aa290a3f-c761-40a0-9c6d-6946c4548f46
-- title:
--   Zero Free Dirichlet: chebyshev character eq zero of le one
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev character eq zero of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L52-L60

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

theorem Formalism.ZeroFreeDirichlet.chebyshev_character_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Schi χ x = 0 := by sorry
