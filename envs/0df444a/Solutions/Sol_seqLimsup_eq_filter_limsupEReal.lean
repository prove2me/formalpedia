-- Prove2me | solution 1 for seqLimsup_eq_filter_limsupEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:32:53.73133+00:00
-- url     : https://prove2.me/submissions/d6119290-6555-47f9-b439-9e2c4d0e9a15

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
    seqLimsup u = Filter.limsup u Filter.atTop := by
  simpa [seqLimsup, tailSup, Nat.add_comm] using
    (Filter.limsup_eq_iInf_iSup_of_nat' (u := u)).symm
