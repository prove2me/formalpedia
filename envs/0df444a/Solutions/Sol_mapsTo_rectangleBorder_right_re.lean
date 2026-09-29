-- Prove2me | solution 1 for mapsTo_rectangleBorder_right_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:29:34.194421+00:00
-- url     : https://prove2.me/submissions/aba4c631-5efa-40d4-b691-3ce2c333e301

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
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]
