-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_corollary_A_4_10
-- name    : ConservativePJ.ManyPlayers.corollary_A_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:32:05.159695+00:00
-- url     : https://prove2.me/theorems/9f005eae-f11d-4eaf-b702-cd75190bf8b8
-- title:
--   Corollary A.4.10 — lower bounds for $\log^*n+s$ players with constants $\beta^2/(256\ln2)$ and $\beta^2/(128\ln2)$
-- statement:
--   **Lower bounds for $\log^*n+s$ players.** Fix $0\le\varepsilon<1$ and put $\beta=1-\varepsilon$. There is $n_\varepsilon$ such that for all integers $n\ge n_\varepsilon$ and $s\ge0$, with $k=\log^*n+s$,
--   $$B_\varepsilon(\widehat{\mathrm{MPJ}}_k)\ge\frac{\beta^2}{256\ln2}\Big(1+\frac n{(s+1)^2}\Big),\qquad T_\varepsilon(\widehat{\mathrm{MPJ}}_k)\ge\frac{\beta^2}{128\ln2}\Big(\frac n{s+1}+\sqrt n\Big).$$
--   The same bounds hold for the maximum and the total communication of every deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$ whose success probability under $\mu$ is at least $\beta$.
--
--   These are the lower bounds of Theorem 1.1(a) with explicit constants.
--
--   Differences from the source:
--   - reading: "There is n_ε such that, for all integers n ≥ n_ε" → `∃ N, ∀ n ≥ N`; reason: explicit quantifier form
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
--   - encoding: B_ε, T_ε = least maximum / total communication of an ε-error protocol → `Bε n k pb ε`, `Tε n k pb ε` = `sInf` over ℕ of the costs of ε-error `RandProtocol`s; reason: the set is nonempty for n ≥ 1, k ≥ 2 (Player 1 lists f_k ∘ ⋯ ∘ f_2), so `sInf` is its least element
--   - encoding: success probability under µ (A_1 uniform on [n], Π_2, …, Π_k uniform on S_n, independent) → `successMu`: number of correct tuples (a_1, π_2, …, π_k) ∈ Fin n × S_n^{k−2} × S_n divided by the cardinality n·(n!)^{k−1}; reason: uniform law on a finite set
--   - encoding: log* n = min{t ≥ 0 : log^(t) n ≤ 1} → `PredAdvice.logStar n` (published definition, `sInf {t | (Real.logb 2)^[t] n ≤ 1}`); reason: the same function
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 46 (PDF 48), Corollary A.4.10 (App. A.4.9); proof p. 46 (PDF 48)

import Mathlib
import Definitions.Def_PredAdvice_logStar
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem corollary_A_4_10 (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℕ,
      (1 - ε) ^ 2 / (256 * Real.log 2) * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ≤
          (Bε n (PredAdvice.logStar n + s) .hat ε : ℝ) ∧
      (1 - ε) ^ 2 / (128 * Real.log 2) * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n) ≤
          (Tε n (PredAdvice.logStar n + s) .hat ε : ℝ) ∧
      ∀ (M : Fin (PredAdvice.logStar n + s - 1) → ℕ)
        (P : DetProtocol n (PredAdvice.logStar n + s) .hat M), 1 - ε ≤ successMu P →
        (1 - ε) ^ 2 / (256 * Real.log 2) * (1 + (n : ℝ) / ((s : ℝ) + 1) ^ 2) ≤
            (maxComm M : ℝ) ∧
        (1 - ε) ^ 2 / (128 * Real.log 2) * ((n : ℝ) / ((s : ℝ) + 1) + Real.sqrt n) ≤
            (totalComm M : ℝ) := by sorry

end ConservativePJ.ManyPlayers
