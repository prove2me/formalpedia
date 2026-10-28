-- Prove2me | Theorems.Thm_BitDFT_descriptor_placement_correct
-- name    : BitDFT.descriptor_placement_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:16:45.95251+00:00
-- url     : https://prove2.me/theorems/93f6cf4d-be72-4fa6-b8d4-e109b640c46c
-- title:
--   Routed descriptor preparation keeps its clock and preserves unused tapes
-- statement:
--   From the explicitly embedded initial configuration, the routed descriptor routine reaches the explicitly embedded final configuration within 2|y|+6 transitions. Every physical tape outside the four selected source-machine tapes preserves its supplied contents and head position. The bound is unchanged by alphabet embedding, tape extension, and permutation. The preparation of the given starting configuration remains a separate obligation.
-- source:
--   Composition of accepted exact machine transformations and charged descriptor setup for the DFT output scaler.

import Definitions.Def_BitDFT_DescriptorPlacement
open BitDFT.DescriptorPlacement BitDFT IntMul

theorem BitDFT.descriptor_placement_correct (N : MultitapeTM) (k : ℕ)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    ∃ t : ℕ, t ≤ 2*y.length+6 ∧
      (machine N k).step^[t] (embed N k cells heads (RewoundDescriptor.initial base y)) =
        embed N k cells heads (RewoundDescriptor.final base y) ∧
      ∀ i : Fin (4+(k+3)), 4 ≤ ((routing k).symm i).val →
        ((machine N k).step^[t] (embed N k cells heads (RewoundDescriptor.initial base y))).cells i = cells i ∧
        ((machine N k).step^[t] (embed N k cells heads (RewoundDescriptor.initial base y))).head i = heads i := by sorry
