-- Prove2me | Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
-- name    : BitDFT.BankedOperandStageProof.coordinate_pair_to_halt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:15:42.326405+00:00
-- url     : https://prove2.me/theorems/cbecde82-6e9b-47e6-a28e-024f77768cbf
-- title:
--   Stage a signed coordinate and dimension as a multiplier operand pair
-- statement:
--   Let a coordinate tape hold a signed record consisting of a sign bit, a high magnitude bit, and a q-bit low part; let another tape hold the binary dimension n with at most q bits. A fixed controller skips the sign and high bit, fills the caller buffer with the zero-padded q-bit encoding of n, writes the separator, rewinds the coordinate, and copies its q low bits. It halts after exactly 2|bin(n)| + 3q + 14 transitions with the caller buffer containing the staged operand pair.
-- source:
--   Exact finite-state execution proof for the operand-pair staging phase used before the reusable tracked multiplier call. The theorem states only this staging run; it does not yet derive the initial frame from the input readers or compose the multiplier call.

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Mathlib.Data.List.GetD
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedOperandStageProof
open IntMul BitDFT.OperandStage BitDFT.MachineSequence BitDFT.BankedOperandStageProofSupport

theorem coordinate_pair_to_halt {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension low : List Bool) (sign high : Bool)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym))
    (hcoordHead : base.head coord = low.length + 3)
    (hq : dimension.length ≤ low.length)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate low.length N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym))
      (dimension.length + 1) = N.blank) :
    (machine N coord dim out hc hd ho hcd hco hdo).step^[
      2 * dimension.length + 3 * low.length + 14]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) =
      ⟨State.halt,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).cells,
        (coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).head⟩ := by sorry
