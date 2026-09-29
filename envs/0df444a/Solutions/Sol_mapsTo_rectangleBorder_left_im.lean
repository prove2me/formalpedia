-- Prove2me | solution 1 for mapsTo_rectangleBorder_left_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:28:00.389696+00:00
-- url     : https://prove2.me/submissions/a07fe2f3-7c3e-4c89-9024-33c08848053f

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
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]
