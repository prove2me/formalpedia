-- Prove2me | solution 1 for maximal_superstable_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:10.772406+00:00
-- url     : https://prove2.me/submissions/5fd7b03c-8934-43a3-9020-b71fdd2b91ae

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
    (h_max : maximal_superstable G c) :
    ∃ (O : CFOrientation G) (hO : acyclic_with_unique_source G O q),
      orientation_to_config G O q hO = c := by
  rcases superstable_dhar h_max.1 with ⟨O, hO, h_ge⟩
  use O, hO
  let c' := orientation_to_config G O q hO
  have h_eq := h_max.2 c' (orientation_config_superstable G O q hO) h_ge
  exact h_eq
