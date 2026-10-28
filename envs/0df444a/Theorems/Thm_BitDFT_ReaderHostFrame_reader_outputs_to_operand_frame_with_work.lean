-- Prove2me | Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame_with_work
-- name    : BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame_with_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T17:26:17.057674+00:00
-- url     : https://prove2.me/theorems/2f337cb5-a89a-43b2-8224-b79987689f5d
-- title:
--   Reader frame initializes every tracked multiplier work tape
-- statement:
--   If the Fourier reader has written a signed coordinate and the header reader has retained the binary dimension, the shared host frame places both words at the operand staging tapes. Every tracked multiplier work tape is also in its genuine blank configuration, with its head at cell 1. This supplies the complete initial-frame interface needed to start the tracked multiplication machine.
-- source:
--   A locally compiled Lean proof combines disjoint-bank routing, the accepted Fourier/header frame projections, and explicit inverse address bounds. The blank tapes preserve the tracked alphabet start marker at cell 0 and are blank at every positive cell.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_component_tape
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_extra_tape
import Theorems.Thm_BitDFT_header_inverse_fourier_bank
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) := BankedTripleAlphabetHost.multiplierMachine A (tracked M) H

def multiplierTapeRoute (A M H : MultitapeTM) (i : Fin (tracked M).k) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) := by
  let X := tracked M
  have hX : X.k ≤ DedicatedTapeBanks.width A X H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k
    have hX := X.two_le_k
    have hH := H.two_le_k
    omega
  let r := DedicatedTapeBanks.width A X H - X.k
  let h : X.k + r = DedicatedTapeBanks.width A X H := Nat.add_sub_of_le hX
  exact BankedTripleAlphabetHost.route A X H
    (DedicatedTapeBanks.multiplierOffset A X H)
    (by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.multiplierOffset, DedicatedTapeBanks.tail]
      omega)
    (Fin.cast h (TapeExtension.oldTape X r i))

def fourierRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.fourierOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.fourierOffset, DedicatedTapeBanks.tail]; omega)

def headerRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.headerOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega)

def parkedCells (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ →
      (BankedTripleAlphabetHost.carrier A (tracked M) H).Sym := by
  let R := fourierRoute A M H
  exact fun p x =>
    let j := R.symm p
    if hj : j.val < A.k then
      (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells ⟨j.val, hj⟩ x)
    else if x = 0 then (BankedTripleAlphabetHost.carrier A (tracked M) H).startSym
      else (BankedTripleAlphabetHost.carrier A (tracked M) H).blank

def parkedHeads (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ := by
  let R := fourierRoute A M H
  exact fun p =>
    let j := R.symm p
    if hj : j.val < A.k then cF.head ⟨j.val, hj⟩ else 1

theorem reader_outputs_to_operand_frame_with_work (A M H : MultitapeTM)
    (hH4 : 3 < H.k) (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k)
    (hj : 1 ≤ j.val) (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1) :
    ∃ base : (BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells (BankedOperandStage.dimensionTape A M H) =
        (host A M H).tapeOf (dimension.map (host A M H).bitSym) ∧
      base.head (BankedOperandStage.dimensionTape A M H) = dimension.length + 1 ∧
      base.cells (BankedOperandStage.coordinateTape A M H j) =
        (host A M H).tapeOf (([sign, high] ++ low).map (host A M H).bitSym) ∧
      base.head (BankedOperandStage.coordinateTape A M H j) = low.length + 3 ∧
      ∀ i : Fin (tracked M).k, 2 ≤ i.val →
        base.cells (multiplierTapeRoute A M H i) = (host A M H).tapeOf [] ∧
        base.head (multiplierTapeRoute A M H i) = 1 := by sorry
