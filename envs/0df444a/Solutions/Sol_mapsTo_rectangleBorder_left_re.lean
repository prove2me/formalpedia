-- Prove2me | solution 1 for mapsTo_rectangleBorder_left_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:28:31.638026+00:00
-- url     : https://prove2.me/submissions/d703f902-bca4-4717-9773-4158cec42a6c

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem solution (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]
