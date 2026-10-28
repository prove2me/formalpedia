-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_one
-- name    : AvramDividend.Classical.deriv_bounded_on_compact_of_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:45:56.276355+00:00
-- url     : https://prove2.me/theorems/c57310fb-0385-4462-8abe-2b223bb5c380
-- title:
--   C1 regularity bounds the first derivative on compact subintervals
-- statement:
--   If a real-valued function is C1 on an open interval (0,a), then its ordinary derivative is bounded in absolute value on every compact subinterval [l,u] strictly inside (0,a). Apply the extreme-value theorem to the continuous first within-derivative on the compact interval and identify it with the ordinary derivative using smoothness in the ambient open neighbourhood. This strengthens the previously Proved C2 compact derivative bound and supports first-order BV generator domination.
-- source:
--   Elementary compactness and C1 calculus, supporting bounded-variation generator estimates for Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set

namespace AvramDividend.Classical

theorem deriv_bounded_on_compact_of_contDiff_one
    (W : ℝ → ℝ) (a l u : ℝ)
    (hlu : l < u) (hsub : Icc l u ⊆ Ioo 0 a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l u, |deriv W x| ≤ C := by sorry

end AvramDividend.Classical
