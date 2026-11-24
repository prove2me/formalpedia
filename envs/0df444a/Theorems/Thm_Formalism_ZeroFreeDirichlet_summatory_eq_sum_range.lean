-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_eq_sum_range
-- name    : Formalism.ZeroFreeDirichlet.summatory_eq_sum_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:41.046256+00:00
-- url     : https://prove2.me/theorems/a5f13d26-d134-44d3-b99f-de3be6d742d6
-- title:
--   Zero Free Dirichlet: summatory eq sum range
-- statement:
--   The Zero Free Dirichlet construction uses the summatory eq sum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L186-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L186-L197

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

theorem Formalism.ZeroFreeDirichlet.summatory_eq_sum_range {a : ℕ → ℝ} (ha0 : a 0 = 0) {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sa a x = ∑ n ∈ Finset.range N, a n * Formalism.mxS n x := by sorry
