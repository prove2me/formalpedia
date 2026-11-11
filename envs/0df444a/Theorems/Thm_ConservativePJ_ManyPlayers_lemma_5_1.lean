-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_5_1
-- name    : ConservativePJ.ManyPlayers.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:49.766624+00:00
-- url     : https://prove2.me/theorems/21c21042-6f63-4f3b-b76d-1bdd53614200
-- title:
--   Lemma 5.1 — success bound for fixed messages: $\beta\le 1/n+\sqrt{(k-1)T\ln2/n}$ under µ
-- statement:
--   **Success bound for fixed messages.** Let $n\ge2$ and $k\ge2$, and let $P$ be a deterministic conservative protocol for $\widehat{\mathrm{MPJ}}_k$ with message lengths $\ell_1,\dots,\ell_{k-1}$ and total communication $T=\ell_1+\cdots+\ell_{k-1}$, whose success probability under $\mu$ (start vertex uniform, layers independent uniform permutations) is at least $\beta>0$. Then
--   $$\beta\le\frac1n+\sqrt{\frac{(k-1)\,T\ln2}{n}}.\tag{6}$$
--
--   Every lower bound of the paper rests on this inequality.
--
--   Differences from the source:
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: success probability under µ (A_1 uniform on [n], Π_2, …, Π_k uniform on S_n, independent) → `successMu`: number of correct tuples (a_1, π_2, …, π_k) ∈ Fin n × S_n^{k−2} × S_n divided by the cardinality n·(n!)^{k−1}; reason: uniform law on a finite set
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 12 (PDF 14), Lemma 5.1; proof App. A.4.1, pp. 34–36 (PDF 36–38)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_5_1 (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (M : Fin (k - 1) → ℕ)
    (P : DetProtocol n k .hat M) (β : ℝ) (hβ : 0 < β) (hsucc : β ≤ successMu P) :
    β ≤ 1 / (n : ℝ) +
      Real.sqrt (((k : ℝ) - 1) * (totalComm M : ℝ) * Real.log 2 / (n : ℝ)) := by sorry

end ConservativePJ.ManyPlayers
