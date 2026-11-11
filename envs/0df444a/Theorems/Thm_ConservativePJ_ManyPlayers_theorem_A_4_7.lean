-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_theorem_A_4_7
-- name    : ConservativePJ.ManyPlayers.theorem_A_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:32:07.376047+00:00
-- url     : https://prove2.me/theorems/86a9a9e6-4ac0-48f5-a03d-7e5398887564
-- title:
--   Theorem A.4.7 — quadratic lower bound for $3\le k\le\log^*n+s$ under µ
-- statement:
--   **Quadratic lower bound.** Let $n\ge2$, $s\ge0$, $3\le k\le\log^*n+s$, $0\le\varepsilon<1$, and $\beta=1-\varepsilon$. Every deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$ whose success probability under $\mu$ is at least $\beta$ has maximum communication $B$ and total communication $T$ with
--   $$B>\frac{\beta^2n}{16(s+2)^2\ln2}-\log n-1-\log\frac4\beta,\tag{26}$$
--   $$T>\frac{\beta^2n}{16(s+2)\ln2}-k(1+\log n)-\log\frac4\beta,\tag{27}$$
--   where $\log=\log_2$.
--
--   It gives the lower bounds of Theorem 1.1(a) when $s\le\log^*n$ (Corollary A.4.10).
--
--   Differences from the source:
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: success probability under µ (A_1 uniform on [n], Π_2, …, Π_k uniform on S_n, independent) → `successMu`: number of correct tuples (a_1, π_2, …, π_k) ∈ Fin n × S_n^{k−2} × S_n divided by the cardinality n·(n!)^{k−1}; reason: uniform law on a finite set
--   - encoding: log (base two) and ln → `Real.logb 2` and `Real.log`; reason: the paper's convention (§2): logarithms are to base two, ln is natural
--   - encoding: log* n = min{t ≥ 0 : log^(t) n ≤ 1} → `PredAdvice.logStar n` (published definition, `sInf {t | (Real.logb 2)^[t] n ≤ 1}`); reason: the same function
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 41 (PDF 43), Theorem A.4.7 (App. A.4.5); proof pp. 41–43 (PDF 43–45)

import Mathlib
import Definitions.Def_PredAdvice_logStar
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem theorem_A_4_7 (n s k : ℕ) (ε : ℝ) (hn : 2 ≤ n) (hk3 : 3 ≤ k)
    (hk : k ≤ PredAdvice.logStar n + s) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (M : Fin (k - 1) → ℕ) (P : DetProtocol n k .hat M) (hsucc : 1 - ε ≤ successMu P) :
    (1 - ε) ^ 2 * (n : ℝ) / (16 * ((s : ℝ) + 2) ^ 2 * Real.log 2) - Real.logb 2 n - 1 -
        Real.logb 2 (4 / (1 - ε)) < (maxComm M : ℝ) ∧
    (1 - ε) ^ 2 * (n : ℝ) / (16 * ((s : ℝ) + 2) * Real.log 2) -
        (k : ℝ) * (1 + Real.logb 2 n) - Real.logb 2 (4 / (1 - ε)) < (totalComm M : ℝ) := by sorry

end ConservativePJ.ManyPlayers
