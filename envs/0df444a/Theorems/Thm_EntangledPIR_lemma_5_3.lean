-- Prove2me | Theorems.Thm_EntangledPIR_lemma_5_3
-- name    : EntangledPIR.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:24.67409+00:00
-- url     : https://prove2.me/theorems/10dc0295-74d5-4598-97f5-88c2cd2e9820
-- title:
--   Lemma 5.3 — correctness of Protocol 1
-- statement:
--   If both servers follow Protocol 1, starting from the Bell pairs of the protocol, then for every index $x\in\{0,1\}^n$ the client accepts and outputs
--
--   $$u\oplus v=F(x)$$
--
--   with probability one.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: instruments, strategies and rounds of §2.1 → Kraus operators with a finite index, `Strategy` per round, the four-round schedule of `clientStep`, messages as bit lists with a bounded alphabet; reason: every finite-dimensional instrument has a Kraus form; over-long messages, all rejected alike, are represented by strings of length `msgBound`; Figure 4 fixes the order of the messages
--   - encoding: the client accepts and outputs $F(x)$ with probability one → the probability that the output of `clientStep` is `some (F x)` equals one, summed over the random string and all branches; reason: the client produces an output only on acceptance
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 5.3, p.27

import Definitions.Def_EntangledPIR_PrivateAgainstA

namespace EntangledPIR

/-- **Lemma 5.3 (Correctness)**, Mantri, manuscript (Nov. 2026), p.27. If both servers follow Protocol 1,
starting from the Bell pairs of the protocol, then for every index `x` the client accepts and outputs
`u ⊕ v = F(x)` with probability one. In `clientStep` an output is produced only on acceptance. -/
theorem lemma_5_3 {n m : ℕ} (lam : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hlam : 1 ≤ lam)
    (F : Bits n → Bits m) (x : Bits n) : successProb lam F x = 1 := by sorry

end EntangledPIR
