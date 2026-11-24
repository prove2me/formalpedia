-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_rpow_integrableOn
-- name    : Formalism.ZeroFreeDirichlet.summatory_rpow_integrableOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:33.806991+00:00
-- url     : https://prove2.me/theorems/f3470d9b-a335-4e01-b875-6c1e5c738e27
-- title:
--   Zero Free Dirichlet: summatory rpow integrable On
-- statement:
--   The Zero Free Dirichlet construction uses the summatory rpow integrable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L218-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L218-L227

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

theorem Formalism.ZeroFreeDirichlet.summatory_rpow_integrableOn {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (Formalism.Sa a x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) := by sorry
