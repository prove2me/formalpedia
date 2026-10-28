-- Prove2me | Theorems.Thm_BitDFT_signed_block_placement_correct
-- name    : BitDFT.signed_block_placement_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:50:27.488984+00:00
-- url     : https://prove2.me/theorems/f000fd68-6daa-495a-a98c-076b44161fd8
-- title:
--   Signed-coordinate extraction in the scaler workspace preserves its clock and parked tapes
-- statement:
--   Given the explicit initialized extraction frame and at least B=val(y)+1 unread magnitude bits, the routed machine copies the sign and magnitude to scratch within 6B+4|y|+4 steps. Its complete final configuration restores both descriptors and advances the vector and scratch heads. Every extra tape retains its original cells and head. Alphabet conversion and tape routing are exact simulations and add no steps; preparing the initial frame is a separate obligation.
-- source:
--   Composition of accepted exact machine transformations and charged descriptor setup for the DFT output scaler.

import Definitions.Def_BitDFT_SignedBlockPlacement
open BitDFT.SignedBlockPlacement BitDFT IntMul

theorem BitDFT.signed_block_placement_correct (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) (hx : val y+1 ≤ x.length) :
    let start := WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.initial pre out sign x y)
    let finish := WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.final pre out sign x y)
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+4 ∧
      (machine N k).step^[t] (embed N k cells heads start) = embed N k cells heads finish ∧
      ∀ i : Fin (5+(k+3)), 5 ≤ ((routing k).symm i).val →
        ((machine N k).step^[t] (embed N k cells heads start)).cells i = cells i ∧
        ((machine N k).step^[t] (embed N k cells heads start)).head i = heads i := by sorry
