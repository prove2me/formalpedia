-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_theorem_1_1
-- name    : ConservativePJ.ManyPlayers.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:32:13.856144+00:00
-- url     : https://prove2.me/theorems/6f9af450-0384-4636-8789-58ff99ed3a84
-- title:
--   Theorem 1.1 — $B_\varepsilon=\Theta(1+n/(s+1)^2)$, $T_\varepsilon=\Theta(n/(s+1)+\sqrt n)$ with $\log^*n+s$ players; $\Theta(1+n/k^2)$, $\Theta(n/k+\sqrt n)$ for $\mathrm{MPJ}_k$
-- statement:
--   **Pointer jumping with many players.** There is an absolute constant $C$ such that for every $0\le\varepsilon<1$ there are $c>0$ and $N$, depending only on $\varepsilon$, with the following properties.
--
--   1. For every $n\ge N$ and every integer $s\ge0$, with $k=\log^*n+s$,
--   $$c\Big(1+\frac n{(s+1)^2}\Big)\le B_\varepsilon(\widehat{\mathrm{MPJ}}_k)\le C\Big(1+\frac n{(s+1)^2}\Big),\qquad c\Big(\frac n{s+1}+\sqrt n\Big)\le T_\varepsilon(\widehat{\mathrm{MPJ}}_k)\le C\Big(\frac n{s+1}+\sqrt n\Big);$$
--   one deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$, correct on every input (every start vertex and arbitrary layers $f_i:[n]\to[n]$), has maximum communication at most $C(1+n/(s+1)^2)$ and total communication at most $C(n/(s+1)+\sqrt n)$; and every deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$ whose success probability under $\mu$ (uniform start vertex, independent uniformly random permutations as layers) is at least $1-\varepsilon$ has maximum communication at least $c(1+n/(s+1)^2)$ and total communication at least $c(n/(s+1)+\sqrt n)$.
--   2. If moreover $\varepsilon<1/2$, then for all $n\ge2$ and $k\ge2$,
--   $$c\Big(1+\frac n{k^2}\Big)\le B_\varepsilon(\mathrm{MPJ}_k)\le C\Big(1+\frac n{k^2}\Big),\qquad c\Big(\frac nk+\sqrt n\Big)\le T_\varepsilon(\mathrm{MPJ}_k)\le C\Big(\frac nk+\sqrt n\Big),$$
--   and one deterministic conservative protocol for $\mathrm{MPJ}_k$, correct on every input, has maximum communication at most $C(1+n/k^2)$ and total communication at most $C(n/k+\sqrt n)$.
--
--   Here $B_\varepsilon$, $T_\varepsilon$ are the least maximum and total communication of an $\varepsilon$-error conservative protocol with public and private coins, the answer of Player $k$ is not counted, and $\log^*n=\min\{t\ge0:\log^{(t)}n\le1\}$ with base-two logarithms. Beyond $\log^*n$ players, the longest message shrinks quadratically and the total communication linearly in the number $s$ of additional players, until the total reaches its floor of order $\sqrt n$; randomness saves at most a constant factor.
--
--   Differences from the source:
--   - reading: "Θ(·)"; "The constants in the lower bounds depend only on ε, and those in the upper bounds are absolute"; "for all sufficiently large n" → `∃ C, ∀ ε ∈ [0,1), ∃ c > 0, ∃ N` with every lower bound ≥ c·(…) and every upper bound ≤ C·(…); N only in part (a); reason: the theorem's own sentence on the constants, written as quantifiers; one c and one C serve all four Θ's (take the min / max)
--   - reading: "In each part, one deterministic conservative protocol that is correct on every input achieves both upper bounds" → in each part, `∃ M P, (∀ x, P.Correct x) ∧ maxComm ≤ C(…) ∧ totalComm ≤ C(…)`; reason: literal
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
--   - encoding: last layer of MPJ_k maps into {0, 1} → `Bool`; reason: relabelling
--   - encoding: B_ε, T_ε = least maximum / total communication of an ε-error protocol → `Bε n k pb ε`, `Tε n k pb ε` = `sInf` over ℕ of the costs of ε-error `RandProtocol`s; reason: the set is nonempty for n ≥ 1, k ≥ 2 (Player 1 lists f_k ∘ ⋯ ∘ f_2), so `sInf` is its least element
--   - encoding: success probability under µ (A_1 uniform on [n], Π_2, …, Π_k uniform on S_n, independent) → `successMu`: number of correct tuples (a_1, π_2, …, π_k) ∈ Fin n × S_n^{k−2} × S_n divided by the cardinality n·(n!)^{k−1}; reason: uniform law on a finite set
--   - encoding: log* n = min{t ≥ 0 : log^(t) n ≤ 1} → `PredAdvice.logStar n` (published definition, `sInf {t | (Real.logb 2)^[t] n ≤ 1}`); reason: the same function
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 2 (PDF 4), Theorem 1.1; upper bounds Theorem 4.4 (p. 12, PDF 14; App. A.3.6, pp. 31–33); lower bounds App. A.4.10 (p. 47, PDF 49)

import Mathlib
import Definitions.Def_PredAdvice_logStar
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem theorem_1_1 :
    ∃ C : ℝ, ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → ∀ s : ℕ,
        c * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ≤ (Bε n (PredAdvice.logStar n + s) .hat ε : ℝ) ∧
        (Bε n (PredAdvice.logStar n + s) .hat ε : ℝ) ≤ C * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ∧
        c * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n) ≤
          (Tε n (PredAdvice.logStar n + s) .hat ε : ℝ) ∧
        (Tε n (PredAdvice.logStar n + s) .hat ε : ℝ) ≤
          C * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n) ∧
        (∃ (M : Fin (PredAdvice.logStar n + s - 1) → ℕ)
            (P : DetProtocol n (PredAdvice.logStar n + s) .hat M),
          (∀ x, P.Correct x) ∧
          (maxComm M : ℝ) ≤ C * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ∧
          (totalComm M : ℝ) ≤ C * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n)) ∧
        (∀ (M : Fin (PredAdvice.logStar n + s - 1) → ℕ)
            (P : DetProtocol n (PredAdvice.logStar n + s) .hat M), 1 - ε ≤ successMu P →
          c * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ≤ (maxComm M : ℝ) ∧
          c * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n) ≤ (totalComm M : ℝ))) ∧
      (ε < 1 / 2 → ∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
        c * (1 + (n : ℝ) / (k : ℝ) ^ 2) ≤ (Bε n k .bool ε : ℝ) ∧
        (Bε n k .bool ε : ℝ) ≤ C * (1 + (n : ℝ) / (k : ℝ) ^ 2) ∧
        c * ((n : ℝ) / (k : ℝ) + Real.sqrt n) ≤ (Tε n k .bool ε : ℝ) ∧
        (Tε n k .bool ε : ℝ) ≤ C * ((n : ℝ) / (k : ℝ) + Real.sqrt n) ∧
        ∃ (M : Fin (k - 1) → ℕ) (P : DetProtocol n k .bool M),
          (∀ x, P.Correct x) ∧
          (maxComm M : ℝ) ≤ C * (1 + (n : ℝ) / (k : ℝ) ^ 2) ∧
          (totalComm M : ℝ) ≤ C * ((n : ℝ) / (k : ℝ) + Real.sqrt n)) := by sorry

end ConservativePJ.ManyPlayers
