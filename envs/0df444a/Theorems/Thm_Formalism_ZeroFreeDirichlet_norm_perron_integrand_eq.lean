-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_perron_integrand_eq
-- name    : Formalism.ZeroFreeDirichlet.norm_perron_integrand_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:13.684252+00:00
-- url     : https://prove2.me/theorems/71dbbe57-8651-453a-b67d-7493eb5c9626
-- title:
--   Zero Free Dirichlet: norm perron integrand eq
-- statement:
--   The Zero Free Dirichlet construction uses the norm perron integrand eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L9-L12

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.norm_perron_integrand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fchi χ y w‖ = ‖negLD χ w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by sorry
