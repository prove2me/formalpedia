-- Prove2me | solution 1 for maximal_superstable_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:16.875434+00:00
-- url     : https://prove2.me/submissions/2be8a8d5-a60a-4ffd-bdd5-05fb3b981930

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) (c : Config G q)
    (h_super : superstable G q c) :
    ∃ c' : Config G q, maximal_superstable G c' ∧ c ≤ c' := by
    rcases superstable_dhar h_super with ⟨O, hO, h_ge⟩
    let c' := orientation_to_config G O q hO
    use c'
    refine ⟨?_, h_ge⟩
    -- Remains to show c' is maximal superstable
    exact orientation_config_maximal G O q hO
