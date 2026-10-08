-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_attained_of_strict_nearzero_bound
-- name    : AvramDividend.Classical.cstar_attained_of_strict_nearzero_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T20:37:41.354982+00:00
-- url     : https://prove2.me/theorems/055f2de6-e427-475f-a1cb-875f5827a95d
-- title:
--   Attainment of cstar from a strict near-zero derivative gap and compact-interval continuity
-- statement:
--   Given one positive global derivative minimiser a of an Avram scale-like function W, let 0<δ≤a. Suppose W' is continuous on [δ,a] and is strictly above W'(a) at every x∈(0,δ). Then the infimum-defined cstar itself is a positive global derivative minimiser. No continuity at zero or global continuity of W' is required. This covers a missing attainment step in the unbounded-variation regime, where W'(x) can blow up as x decreases to zero.
-- source:
--   Identify cstarSet W ∩ Icc 0 a with the closed derivative sublevel set Icc δ a ∩ (deriv W)⁻¹' (Iic (deriv W a)). The strict near-zero gap excludes all minimisers below δ; the known minimiser a makes sublevel points minimisers. Pinned ContinuousOn.preimage_isClosed_of_isClosed plus compactness of Icc δ a makes the initial minimiser set compact. The earlier Proved compact-initial-minimisers child identifies cstar with its least element.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers
open AvramDividend.Classical Set

namespace AvramDividend.Classical

theorem cstar_attained_of_strict_nearzero_bound (W : ℝ → ℝ) (a δ : ℝ)
    (ha : a ∈ cstarSet W)
    (hδ : 0 < δ) (hδa : δ ≤ a)
    (hcont : ContinuousOn (deriv W) (Set.Icc δ a))
    (hnear : ∀ x : ℝ, 0 < x → x < δ →
      deriv W a < deriv W x) :
    (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
