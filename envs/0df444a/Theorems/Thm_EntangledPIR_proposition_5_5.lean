-- Prove2me | Theorems.Thm_EntangledPIR_proposition_5_5
-- name    : EntangledPIR.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:24.796808+00:00
-- url     : https://prove2.me/theorems/3819d009-73b5-4646-8cd3-703ec6f9d70e
-- title:
--   Proposition 5.5 — perfect privacy against B
-- statement:
--   Protocol 1 is perfectly private against B. For every initial state of the servers, every strategy of B, every round and all indices $x,x'$, with A and the client following the protocol,
--
--   $$D\bigl(\mathrm{View}_{\mathsf B}(x),\mathrm{View}_{\mathsf B}(x')\bigr)=0 .$$
--
--   The queries enter only operations of the honest A whose outcomes are never sent to B.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: instruments, strategies and rounds of §2.1 → Kraus operators with a finite index, `Strategy` per round, the four-round schedule of `clientStep`, messages as bit lists with a bounded alphabet; reason: every finite-dimensional instrument has a Kraus form; over-long messages, all rejected alike, are represented by strings of length `msgBound`; Figure 4 fixes the order of the messages
--   - encoding: the view, including timing and termination (p.11, A.1) → a classical-quantum matrix on history × register, after every round $r\le 4$, with a fixed schedule that continues with empty messages after an abort, and $r=0$ included; reason: the round is the timing; abort shows in the history; later operations are channels independent of the index and idle strategies recover the view at the end of the execution; at $r=0$ the two views coincide
--   - encoding: $D\le0$ → `DimFreeShadow.traceDistance … ≤ 0`, for $\varepsilon=0$ of Definition 2.1; reason: the literal condition of the definition; a trace norm is nonnegative
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Proposition 5.5, p.27; proof p.58

import Definitions.Def_EntangledPIR_PrivateAgainstA

namespace EntangledPIR

/-- **Proposition 5.5 (Privacy against B)**, Mantri, manuscript (Nov. 2026), p.27: Protocol 1 is perfectly
private against B. For every initial state and strategy of B, with A and the client following the protocol,
the views of B on any two indices have trace distance `0` at every round. -/
theorem proposition_5_5 {n m : ℕ} (lam : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hlam : 1 ≤ lam)
    (F : Bits n → Bits m) : PrivateAgainstB lam F 0 := by sorry

end EntangledPIR
