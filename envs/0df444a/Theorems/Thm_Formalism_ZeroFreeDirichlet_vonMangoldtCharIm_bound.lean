-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharIm_bound
-- name    : Formalism.ZeroFreeDirichlet.vonMangoldtCharIm_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:26.947811+00:00
-- url     : https://prove2.me/theorems/91ea0986-bb6c-46cb-8390-715c8158bced
-- title:
--   Zero Free Dirichlet: von Mangoldt Char Im bound
-- statement:
--   The Zero Free Dirichlet construction uses the von Mangoldt Char Im bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L29-L37

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

theorem Formalism.ZeroFreeDirichlet.vonMangoldtCharIm_bound (n : ℕ) : |vonMangoldtCharIm χ n| ≤ 1 * Λ n := by sorry
