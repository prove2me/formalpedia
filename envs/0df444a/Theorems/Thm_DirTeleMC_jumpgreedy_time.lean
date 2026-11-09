-- Prove2me | Theorems.Thm_DirTeleMC_jumpgreedy_time
-- name    : DirTeleMC.jumpgreedy_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:36:34.356622+00:00
-- url     : https://prove2.me/theorems/a812a553-c452-45c0-b9cd-e846ba9a0163
-- title:
--   Proof of Theorem 1.1, p.31 — JUMPGREEDY runs in time $n^{O(\ell)}$
-- statement:
--   There is an absolute constant $c$ such that for every integer $\ell \ge 2$ there is a function $\mathrm{alg}$ on instances, computed by a Turing machine whose number of steps on an input of length $m$ is at most $(m+2)^{c\ell}$ for every $m$, such that on every well-formed instance the output of $\mathrm{alg}$ is a schedule that JUMPGREEDY with parameter $\ell$ can return.
--
--   Instances are encoded with their $n \times n$ adjacency matrix, so $m \ge n^2$ and the bound is $n^{O(\ell)}$.
--
--   Differences from the source:
--   - reading: runs in n^{O(ℓ)} time → one Mathlib Turing machine (TM2ComputableInTime) per ℓ with time at most (m + 2)^{c·ℓ} on every input of length m, c fixed before ℓ; reason: the source names no machine model; one exponent constant uniform in ℓ is the meaning of n^{O(ℓ)}
--   - encoding: an instance of unstated input size → the encoding encInst with the n × n adjacency matrix, so n² ≤ m; reason: with this encoding (m + 2)^{O(ℓ)} and n^{O(ℓ)} are the same bound
--   - encoding: the algorithm JUMPGREEDY → a function whose output on every well-formed instance is the output of a run of the relation JumpGreedyRun; reason: the relation leaves only the page's open ties open
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), proof of Theorem 1.1, "Running time", p.31 (PDF p.32)

import Mathlib
import Definitions.Def_DirTeleMC_JumpGreedyRun
import Definitions.Def_DirTeleMC_encInst

namespace DirTeleMC

/-- **The running-time half of the proof of Theorem 1.1.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), proof of Theorem 1.1, "Running time", p.31: "Every iteration of the while loop (line 3 of Algorithm 1) counts
at least one terminal and the demand is at most k, so a call makes at most k iterations. … Hence a call at height
h takes time t_h ≤ kn(t_{h−1} + poly(n)), line 6 of Algorithm 2 makes (kn)^η poly(n) = n^{O(ℓ)} arithmetic
operations, and the loop in line 4 of Algorithm 2 makes k − 1 iterations. … As µ ≤ 20ηℓ(2k + 1), every number has
a numerator and a denominator of n^{O(ℓ)} bits, every operation takes time n^{O(ℓ)}, and the total running time is
n^{O(ℓ)}."

There is an absolute constant `c` such that for every `ℓ ≥ 2` there is a function `alg`, computed by a Turing
machine (Mathlib's `TM2ComputableInTime` over the encodings `encInst`, `encSched`) whose time on inputs of length
`m` is at most `(m + 2)^{c·ℓ}` for every `m`, such that on every well-formed instance the output of `alg` is the
schedule returned by a run of JUMPGREEDY with parameter `ℓ`.

**Formalization Note.** "n^{O(ℓ)} time" is read as one machine per `ℓ` (JUMPGREEDY with parameter `ℓ`) and one
exponent constant `c` fixed before `ℓ`. The input length `m` of an instance is at least `n²` (the adjacency matrix),
so `(m + 2)^{c·ℓ}` is `n^{O(ℓ)}`. The time bound holds on every input, including instances that are not
well-formed, on which the output is not constrained. Outputs are schedules with vertices written as numbers. -/
theorem jumpgreedy_time :
    ∃ c : ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ → ∃ alg : Inst → List (List (ℕ × ℕ)),
      (∃ M : Turing.TM2ComputableInTime encInst encSched alg, ∀ m, M.time m ≤ (m + 2) ^ (c * ℓ)) ∧
      ∀ I : Inst, I.WF → ∃ S : Schedule I.n, alg I = S.toNat ∧ JumpGreedyRun ℓ I S := by sorry

end DirTeleMC
