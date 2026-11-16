-- Prove2me | solution 1 for thm_3_7
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:10.451891+00:00
-- url     : https://prove2.me/submissions/c5f99c64-42a3-4c73-bdb6-b59819cdbc2a

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem

open MeasurableSpace


/--

  ## Theorem 3.7 pi-lambda theorem

-/
theorem solution {α : Type*} {P : Set (Set α)} {L : DynkinSystem α}
  (hP : IsPiSystem P) (hPL : ∀ s ∈ P, L.Has s) :
  ∀ s, @MeasurableSet α (generateFrom P) s → L.Has s := by
  intro s hs
  rw [MeasurableSpace.DynkinSystem.generateFrom_eq hP] at hs
  exact MeasurableSpace.DynkinSystem.generate_le L hPL s hs

