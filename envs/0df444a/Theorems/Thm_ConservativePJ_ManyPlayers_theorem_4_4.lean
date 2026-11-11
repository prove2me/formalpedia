-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_theorem_4_4
-- name    : ConservativePJ.ManyPlayers.theorem_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:32:01.030611+00:00
-- url     : https://prove2.me/theorems/97c4b3e7-44e6-4b71-a20a-e813199ab2cb
-- title:
--   Theorem 4.4 — deterministic protocols, correct on every input, meeting the upper bounds of Theorem 1.1 with one absolute $C$
-- statement:
--   **Deterministic protocols.** There is a constant $C$ such that:
--
--   1. for all sufficiently large $n$ and every integer $s\ge0$, with $k=\log^*n+s$, some deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$ is correct on every input (every start vertex and arbitrary layers $f_i:[n]\to[n]$) and has
--   $$\text{maximum communication}\le C\Big(1+\frac n{(s+1)^2}\Big),\qquad\text{total communication}\le C\Big(\frac n{s+1}+\sqrt n\Big);$$
--   2. for all $n\ge2$ and $k\ge2$, some deterministic conservative protocol for $\mathrm{MPJ}_k$ is correct on every input and has maximum communication at most $C(1+n/k^2)$ and total communication at most $C(n/k+\sqrt n)$.
--
--   This gives the upper bounds of Theorem 1.1 for every $0\le\varepsilon<1$.
--
--   Differences from the source:
--   - reading: "There is a constant C … for all sufficiently large n" → `∃ C`, then `∃ N, ∀ n ≥ N` in (a); no threshold in (b); reason: explicit quantifier form; C is the same in (a) and (b)
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: last layer of MPJ_k maps into {0, 1} → `Bool`; reason: relabelling
--   - encoding: log* n = min{t ≥ 0 : log^(t) n ≤ 1} → `PredAdvice.logStar n` (published definition, `sInf {t | (Real.logb 2)^[t] n ≤ 1}`); reason: the same function
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 12 (PDF 14), Theorem 4.4; proof App. A.3.6, pp. 32–33 (PDF 34–35)

import Mathlib
import Definitions.Def_PredAdvice_logStar
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem theorem_4_4 :
    ∃ C : ℝ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℕ,
        ∃ (M : Fin (PredAdvice.logStar n + s - 1) → ℕ)
          (P : DetProtocol n (PredAdvice.logStar n + s) .hat M),
          (∀ x, P.Correct x) ∧
          (maxComm M : ℝ) ≤ C * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ∧
          (totalComm M : ℝ) ≤ C * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n)) ∧
      (∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
        ∃ (M : Fin (k - 1) → ℕ) (P : DetProtocol n k .bool M),
          (∀ x, P.Correct x) ∧
          (maxComm M : ℝ) ≤ C * (1 + (n : ℝ) / (k : ℝ) ^ 2) ∧
          (totalComm M : ℝ) ≤ C * ((n : ℝ) / (k : ℝ) + Real.sqrt n)) := by sorry

end ConservativePJ.ManyPlayers
