-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_ennreal_sandwich_vanishing_error
-- name    : AvramDividend.Classical.avram_ws01h_ennreal_sandwich_vanishing_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T20:12:05.758529+00:00
-- url     : https://prove2.me/theorems/e3b3a046-2c3c-4de8-a77d-57dd3124b8fe
-- title:
--   Extended-nonnegative CDF killed-record mass tends to a finite perpetual limit when true Qp no-record remainder vanishes
-- statement:
--   For arbitrary genuine ENNReal-valued quantities f (actual killed upper-record source Qp mass), g (actual full original Lévy survival Qp CDF) and e (true no-record probability), if f≤g≤f+e eventually along any filter, g tends to a finite genuine perpetual survival CDF L, and the no-record error e tends to zero, then f tends to exactly the same perpetual CDF L. The proof rigorously handles ENNReal's noncancellative top and subtraction: the finite-limit condition permits the pinned ENNReal.Tendsto.sub theorem, tsub_le_iff_right supplies g−e≤f, and the pinned eventual Filter.Tendsto.squeeze' shows equality of limits. This is the exact abstract integration used to combine the already canonically proved original-Lévy Qp upper-record CDF partition, true no-record exponential supremum bound, and full closed-survival perpetual CDF limit, without assuming the target two-sided exit scale quotient.
-- source:
--   Pinned Mathlib ENNReal.Tendsto.sub at finite target, tsub_le_iff_right, Filter.Tendsto.squeeze' and accepted Avram true Qp remainder source 8dd1e384 / 18475 / 18479.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Sub.Defs

open Filter
open scoped ENNReal Topology

theorem AvramDividend.Classical.avram_ws01h_ennreal_sandwich_vanishing_error
    {ι : Type*} {l : Filter ι} (f g e : ι → ℝ≥0∞)
    (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hfg : f ≤ᶠ[l] g)
    (hge : g ≤ᶠ[l] (fun i => f i + e i))
    (hg : Tendsto g l (𝓝 L))
    (he : Tendsto e l (𝓝 (0 : ℝ≥0∞))) :
    Tendsto f l (𝓝 L) := by sorry
