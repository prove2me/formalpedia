-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_theorem_4_3
-- name    : ConservativePJ.ManyPlayers.theorem_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:49.535202+00:00
-- url     : https://prove2.me/theorems/c13584de-4c5a-4b51-a9d2-aeb830721f39
-- title:
--   Theorem 4.3 — randomized upper bound with $\log^* n+s$ players for $\widehat{\mathrm{MPJ}}_k$
-- statement:
--   **Upper bound with $\log^*n+s$ players.** For every $0<\varepsilon<1$ there are constants $C_\varepsilon$ and $n_\varepsilon$ such that for every $n\ge n_\varepsilon$ and every integer $s\ge0$, with $k=\log^*n+s$, there is an $\varepsilon$-error public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_k$ with
--   $$\text{maximum communication}\le C_\varepsilon\Big(1+\frac n{(s+1)^2}\Big),\qquad \text{total communication}\le C_\varepsilon\Big(\frac n{s+1}+\sqrt n\Big).$$
--   Here $\log^*n=\min\{t\ge0:\log^{(t)}n\le1\}$ with base-two iterated logarithms.
--
--   It is the randomized starting point of the deterministic protocols for $\widehat{\mathrm{MPJ}}_k$ in Theorem 4.4(a).
--
--   Differences from the source:
--   - reading: "there are constants C_ε and n_ε" / "for all sufficiently large n" → `∃ C N, ∀ n ≥ N, …` with C, N chosen after ε and before n, s; reason: the explicit quantifier form of the sentence
--   - encoding: log* n = min{t ≥ 0 : log^(t) n ≤ 1} → `PredAdvice.logStar n` (published definition, `sInf {t | (Real.logb 2)^[t] n ≤ 1}`); reason: the same function
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 11 (PDF 13), Theorem 4.3; proof App. A.3.5, pp. 29–31 (PDF 31–33)

import Mathlib
import Definitions.Def_PredAdvice_logStar
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem theorem_4_3 :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (C : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → ∀ s : ℕ,
      ∃ (M : Fin (PredAdvice.logStar n + s - 1) → ℕ)
        (R : RandProtocol n (PredAdvice.logStar n + s) .hat M), R.IsEpsError ε ∧
        (maxComm M : ℝ) ≤ C * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ∧
        (totalComm M : ℝ) ≤ C * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n) := by sorry

end ConservativePJ.ManyPlayers
