-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_iterate_segments
-- name    : BitDFT.MachineSequence.iterate_segments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:53:38.548133+00:00
-- url     : https://prove2.me/theorems/07df12ce-e018-4a1f-8a8e-8dca5c817040
-- title:
--   Compose the exact clocks of a sequence of machine segments
-- statement:
--   Let a deterministic transition function carry configurations c_0,c_1,…. Suppose segment i takes exactly t_i transitions from c_i to c_{i+1}. Then after the sum of the first n segment lengths, the machine is exactly at c_n:
--   \[f^{\sum_{i<n}t_i}(c_0)=c_n.\]
--   This gives an exact global clock for a finite sequence of scan-and-call stages, including any fixed dispatch or return transitions charged inside each segment.
-- source:
--   Finite composition principle for repeated scalar-multiplier calls in the DFT rescaling construction.

import Definitions.Def_BitDFT_MachineSequence
set_option autoImplicit false

theorem BitDFT.MachineSequence.iterate_segments {α : Type} (f : α → α) (cfg : ℕ → α) (cost : ℕ → ℕ)
    (hsegment : ∀ i, f^[cost i] (cfg i) = cfg (i + 1)) (n : ℕ) :
    f^[∑ i ∈ Finset.range n, cost i] (cfg 0) = cfg n := by sorry
