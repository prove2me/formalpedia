-- Prove2me | solution 1 for seqLiminf_eq_filter_liminfEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:32:46.296192+00:00
-- url     : https://prove2.me/submissions/65cf04ea-0205-42d1-80f4-a90f16b1eec2

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology

theorem solution (u : ℕ → EReal) :
    seqLiminf u = Filter.liminf u Filter.atTop := by
  simpa [seqLiminf, tailInf, Nat.add_comm] using
    (Filter.liminf_eq_iSup_iInf_of_nat' (u := u)).symm
