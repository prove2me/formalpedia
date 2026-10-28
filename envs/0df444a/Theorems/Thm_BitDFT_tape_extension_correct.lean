-- Prove2me | Theorems.Thm_BitDFT_tape_extension_correct
-- name    : BitDFT.tape_extension_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:34:53.927065+00:00
-- url     : https://prove2.me/theorems/574a2a6a-9bbf-4ba3-9709-71f17e6ea2a0
-- title:
--   Extra parked tapes preserve complete machine executions at the same clock
-- statement:
--   For any multitape machine M and any fixed number r of extra tapes, every t-step execution of the extended machine agrees exactly with the original t-step execution on the original tapes and preserves all extra tape cells and heads. This holds for arbitrary starting configurations and arbitrary data on the extra tapes. On ordinary binary inputs, the original and extended machines halt with precisely the same output at precisely the same clocks. Thus adding wrapper workspace causes no simulation slowdown.
-- source:
--   Induction on the exact multitape transition semantics. The embedding retains the original state, tapes and heads while inserting caller-specified extra tape contents. This is a machine adapter and does not assert completion of the Fourier construction.

import Definitions.Def_BitDFT_TapeExtension
open BitDFT.TapeExtension IntMul

theorem BitDFT.tape_extension_correct (M : MultitapeTM) (r : ℕ) :
    (∀ cells : Fin (M.k+r) → ℕ → M.Sym, ∀ heads : Fin (M.k+r) → ℕ,
      ∀ c : M.Cfg, ∀ t : ℕ,
      (machine M r).step^[t] (embed M r cells heads c) =
        embed M r cells heads (M.step^[t] c)) ∧
    (∀ x y w : List Bool, ∀ t : ℕ,
      (machine M r).HaltsWithOutput x y t w ↔ M.HaltsWithOutput x y t w) := by sorry
