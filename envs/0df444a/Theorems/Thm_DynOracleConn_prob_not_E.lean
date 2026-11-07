-- Prove2me | Theorems.Thm_DynOracleConn_prob_not_E
-- name    : DynOracleConn.prob_not_E
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:45.941196+00:00
-- url     : https://prove2.me/theorems/0cfa3960-1a76-4fc8-a268-11aed4b66599
-- title:
--   §3.2.1, p.21 — $\mathbb P_{I^t}[\bar{\mathcal E}\mid\pi,z]\le1/16$
-- statement:
--   Let $1\le B\le d/128$ and $\ell=\lfloor d/(64B)\rfloor$. For every bijection $\pi$ of $[d]$, among the $d^{512B}$ blocks $I^t$ of $512B$ uniform queries, the fraction on which fewer than $16B$ red intervals are occupied is at most
--
--   $$\frac1{16}.$$
--
--   The bound holds for each fixed $(\pi,z)$, which allows later steps to condition on the instance.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - encoding: probability over uniform (π, z), blocks or offsets → a count of outcomes; reason: the outcome spaces are finite and uniform; same statement
--   - generalization: standing 10 ≤ B (§3.1, p.20) → 1 ≤ B; reason: the bound holds for 1 ≤ B and specializes to 10 ≤ B
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.2.1, p.21

import Mathlib
import Definitions.Def_DynOracleConn_Blocks

namespace DynOracleConn

/-- **§3.2.1, p.21 — ℰ fails with probability at most 1/16.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.2.1, p.21: "A fixed red
interval is empty with probability (1 − ℓ/d)^{512B} ≤ e^{−512Bℓ/d} ≤ e^{−4}. Thus the expected number
of empty red intervals is at most 32e^{−4}B. Let ℰ be the event that at least 16B red intervals
(i.e., at least half of them) are occupied. By Markov's inequality, P_{Iᵗ}[ℰ̄ | π, z] =
P_{Iᵗ}[more than 16B red intervals are empty | π, z] ≤ 32e^{−4}B/(16B) = 2e^{−4} ≤ 1/16."

For `1 ≤ B ≤ d/128` and every bijection `π`, among the `d^{512B}` blocks `I` of uniform queries at
most a sixteenth miss ℰ.

**Formalization Note.** The probability over the uniform block is a count over
`Fin (512B) → Fin d`. The paper's standing assumption is `10 ≤ B`; the bound holds for `1 ≤ B`. -/
theorem prob_not_E {d B : ℕ} (hB : 1 ≤ B) (hBd : 128 * B ≤ d) (π : Equiv.Perm (Fin d)) :
    (Set.ncard {I : Fin (512 * B) → Fin d | ¬ EventE d B π I} : ℝ) ≤ (d : ℝ) ^ (512 * B) / 16 := by sorry

end DynOracleConn
