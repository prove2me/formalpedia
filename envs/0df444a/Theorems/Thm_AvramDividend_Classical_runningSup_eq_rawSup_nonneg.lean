-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
-- name    : AvramDividend.Classical.runningSup_eq_rawSup_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T08:18:35.53361+00:00
-- url     : https://prove2.me/theorems/992246e6-0bba-4d6f-bd75-5b29c32037f9
-- title:
--   The running supremum is the raw path supremum over [0, t] and is nonnegative
-- statement:
--   The running supremum of a spectrally negative Lévy process at the base law is the raw path
--   supremum, and is nonnegative. This is the deterministic bridge used by Proposition 1, eq. (3.12)
--   and eq. (3.13), of Avram, Palmowski and Pistorius, arXiv:math/0702893v1, p. 8, at the boundary
--   `x = a`.
--
--   The platform defines `runningSup X t ω = ⨆ s : Icc 0 t, maxZero (X.X s ω)` with
--   `maxZero c = max c 0`, i.e. the paper's `S_t = sup_{0 ≤ s ≤ t} (X_s ∨ 0)` (p. 7, §3.3). Since
--   `X_0 = 0`, the point `s = 0` contributes `max 0 0 = 0`, so this truncated supremum equals the raw
--   supremum `⨆ s : Icc 0 t, X_s` and is nonnegative. No translated law is involved at the boundary.
--
--   Boundedness above of the path image is obtained from the standing right-continuity assumption
--   `X.rightCont`, which makes the path upper semicontinuous on `Ici 0`, combined with compactness of
--   the closed interval `Icc 0 t` via `UpperSemicontinuousOn.bddAbove_of_isCompact`. This is the
--   boundedness content that a càdlàg path enjoys on a compact interval; it is stated here directly
--   from upper semicontinuity because the pinned Mathlib revision carries no càdlàg class.
--
--   **Formalization Note.** The platform's `runningSup` truncates the path at zero from above exactly
--   as in the paper. The statement records both the identification with the raw supremum over the
--   closed interval and the resulting nonnegativity, since the nonnegativity is what turns the
--   truncation into the identity.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, section 3.3 (p. 7), as used in Proposition 1 eq. (3.12)-(3.13) on p. 8 at the boundary x = a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem runningSup_eq_rawSup_nonneg {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) :
    (runningSup X t ω = ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω) ∧
      0 ≤ runningSup X t ω := by sorry

end AvramDividend.Classical
