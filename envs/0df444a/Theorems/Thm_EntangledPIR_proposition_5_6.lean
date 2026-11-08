-- Prove2me | Theorems.Thm_EntangledPIR_proposition_5_6
-- name    : EntangledPIR.proposition_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:32.46358+00:00
-- url     : https://prove2.me/theorems/e6bf407d-36d4-4477-8ea3-cf68c9feed49
-- title:
--   Proposition 5.6 — $2^{-\lambda}$-privacy against A
-- statement:
--   Protocol 1 is $2^{-\lambda}$-private against A: for every initial state, every strategy of A, every round and all indices $x,x'$, with B and the client following the protocol,
--
--   $$D\bigl(\mathrm{View}_{\mathsf A}(x),\mathrm{View}_{\mathsf A}(x')\bigr)\le2^{-\lambda}.$$
--
--   Moreover, the condition of Definition 2.1 holds with $\varepsilon=0$ at the end of every round before the client sends $t$ and $K_1,\dots,K_k$ to A. The privacy error comes from the cut-and-choose bound with four copies of each query.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: instruments, strategies and rounds of §2.1 → Kraus operators with a finite index, `Strategy` per round, the four-round schedule of `clientStep`, messages as bit lists with a bounded alphabet; reason: every finite-dimensional instrument has a Kraus form; over-long messages, all rejected alike, are represented by strings of length `msgBound`; Figure 4 fixes the order of the messages
--   - encoding: the view, including timing and termination (p.11, A.1) → a classical-quantum matrix on history × register, after every round $r\le 4$, with a fixed schedule that continues with empty messages after an abort, and $r=0$ included; reason: the round is the timing; abort shows in the history; later operations are channels independent of the index and idle strategies recover the view at the end of the execution; at $r=0$ the two views coincide
--   - encoding: the end of every round before the client sends $t$ and $K$ to A → `RoundPrivateAgainstA … r 0` for $r\le3$, with $r$ the number of rounds done; reason: that message is the client's message of round 3 of the schedule, counting from 0
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Proposition 5.6, p.28; proof pp.58–60

import Definitions.Def_EntangledPIR_PrivateAgainstA

namespace EntangledPIR

/-- **Proposition 5.6 (Privacy against A)**, Mantri, manuscript (Nov. 2026), p.28: Protocol 1 is
`2^{-λ}`-private against A. Moreover, the condition of Definition 2.1 holds with `ε = 0` at the end of every
round before the client sends `t` and `K_1, …, K_k` to A: in the schedule of `clientStep` that message is the
client's message of round `3`, so these are the views after `r ≤ 3` rounds (`r` counts the rounds done). -/
theorem proposition_5_6 {n m : ℕ} (lam : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hlam : 1 ≤ lam)
    (F : Bits n → Bits m) :
    PrivateAgainstA lam F ((2 : ℝ) ^ lam)⁻¹ ∧ ∀ r, r ≤ 3 → RoundPrivateAgainstA lam F r 0 := by sorry

end EntangledPIR
