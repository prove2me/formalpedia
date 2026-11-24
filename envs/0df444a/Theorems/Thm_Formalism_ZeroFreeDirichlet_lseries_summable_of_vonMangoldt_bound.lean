-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_lseries_summable_of_vonMangoldt_bound
-- name    : Formalism.ZeroFreeDirichlet.lseries_summable_of_vonMangoldt_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:43:00.630655+00:00
-- url     : https://prove2.me/theorems/054385e3-586b-4bc0-96f7-07f90fdc3a34
-- title:
--   Zero Free Dirichlet: lseries summable of von Mangoldt bound
-- statement:
--   The Zero Free Dirichlet construction uses the lseries summable of von Mangoldt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L67-L81

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

theorem Formalism.ZeroFreeDirichlet.lseries_summable_of_vonMangoldt_bound {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (a n : ℂ)) w := by sorry
