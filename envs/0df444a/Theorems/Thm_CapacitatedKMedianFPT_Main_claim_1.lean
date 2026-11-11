-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_claim_1
-- name    : CapacitatedKMedianFPT.Main.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:00.190209+00:00
-- url     : https://prove2.me/theorems/b851f771-1a98-4c42-8aa7-ae4e2c3581c0
-- title:
--   Claim 1 — the leader candidates number O(k log n/ε²) and L has n(k/ε)^{O(k)} entries
-- statement:
--   Let $I$ be an instance whose distances between distinct points are positive integers at most $D=\lceil10n^2/\varepsilon\rceil$, $0<\varepsilon<1/2$, $(S,\varphi)$ a $3$-approximate solution of the underlying uncapacitated instance, $b_s$ nearest clients of the facilities $s\in S$, and $H$ a greedy hitting set of $\mathcal A=\{B_C(f,r_f):f\in F\}$. Then the set $H\cup\{b_s:s\in S\}$ of Algorithm 1 has
--   $$O\Bigl(\frac{k\log n}{\varepsilon^2}\Bigr)$$
--   points, and the list $L$ has $n\,(k/\varepsilon)^{O(k)}$ entries.
--
--   Both $O$'s hide one absolute constant $c$, the same for all instances, all $k$ and all $\varepsilon$. The bound on $L$ is what makes the leader enumeration FPT.
--
--   **Formalization Note** $\log n$ is written $\log\max(2,n)$ (equal for $n\ge2$; at $n=1$ the hypotheses cannot hold). The hypotheses cannot be met when $C=\emptyset$, where $b_s$ is undefined, as in the source.
--
--   Differences from the source:
--
--   - encoding: O(k log n/ε²) and n (k/ε)^O(k) → c·k·log max(2, n)/ε² and n·(k/ε)^{c·k} with one absolute c > 0 chosen first; reason: the meaning of O with a universal constant; k/ε > 2 here
--   - encoding: the set H (after line 9) → `leaderCandidates`, the greedy set together with the nearest clients b_s; reason: line 9 adds the b_s to H
--   - generalization: the hitting set H of the greedy algorithm, b_s ∈ argmin, one run of Algorithm 1 → every greedy run (any tie-breaking), every choice of nearest clients b_s and every 3-approximate uncapacitated solution (S, φ); reason: the source fixes no tie-breaking; its run is one of those covered
--   - reading: line 3 sets p_c = d(c, φ(c))/Q, undefined when Q = 0 (possible when C and F overlap, e.g. C = F = {a, b}, k = 2, d(a, b) = 1, U_a = 0, U_b = 2: feasible with OPT = 1 but Q = 0) → when Q = 0 the leader candidates are C ∪ {b_s} (H := C) and no greedy run is required; reason: the only completion that keeps every client available as a leader; when Q = 0 every client is an open facility of S, so |C| ≤ k
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 7, Claim 1 and proof; p. 9, Algorithm 1

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Leaders

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Claim 1** (p. 7). For an instance with positive integer distances at most `D = ⌈10n²/ε⌉`,
any 3-approximate uncapacitated solution `(S, φ)`, any nearest clients `b_s`, and any greedy hitting
set `H` of `A` (needed only when `Q ≠ 0`), the leader candidates of Algorithm 1 number
`O(k log n / ε²)` and the list `L` has `n (k/ε)^{O(k)}` entries, with one absolute constant `c`. -/
theorem claim_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (S : Finset P)
        (φ b : P → P) (H : Finset P),
        I.IsValid → 0 < ε → ε < 1 / 2 → I.HasIntDistancesUpTo (distanceBound I.size ε) →
        I.IsUncapApprox 3 S φ → I.IsNearestClientChoice S b →
        (I.cost φ ≠ 0 → I.IsGreedyHittingSet (I.ballSystem ε φ) H) →
        ((I.leaderCandidates S φ b H).card : ℝ) ≤
            c * I.k * Real.log (max 2 (I.size : ℝ)) / ε ^ 2 ∧
          ((I.leaderList ε S φ b H).card : ℝ) ≤ I.size * ((I.k : ℝ) / ε) ^ (c * I.k) := by sorry

end CapacitatedKMedianFPT.Main
