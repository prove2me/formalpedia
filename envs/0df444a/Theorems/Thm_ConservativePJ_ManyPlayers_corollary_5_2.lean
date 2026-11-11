-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_corollary_5_2
-- name    : ConservativePJ.ManyPlayers.corollary_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:32:03.490048+00:00
-- url     : https://prove2.me/theorems/f5db9cab-1cd9-4e09-89b4-e8105271d4aa
-- title:
--   Corollary 5.2 — success bound for $\mathrm{MPJ}_k$ under $\mu_{\mathrm{bool}}$, and $T$, $B$ lower bounds for ε-error protocols
-- statement:
--   **Success bound for $\mathrm{MPJ}_k$.** Let $n\ge2$ and $k\ge2$.
--
--   1. Every deterministic conservative protocol for $\mathrm{MPJ}_k$ with total communication $T$ has success probability under $\mu_{\mathrm{bool}}$ at most
--   $$\frac12+\sqrt{\frac{(k-3/2)\,T\ln2}{n}}.$$
--   2. Let $0\le\varepsilon<1/2$. Every $\varepsilon$-error conservative protocol for $\mathrm{MPJ}_k$ with public and private coins, maximum communication $B$ and total communication $T$ satisfies
--   $$T\ge\frac{(1/2-\varepsilon)^2\,n}{(k-3/2)\ln2},\qquad B\ge\frac{(1/2-\varepsilon)^2\,n}{(k-1)(k-3/2)\ln2}.$$
--
--   Part 2 gives $T_\varepsilon(\mathrm{MPJ}_k)=\Omega(n/k)$ and is one half of the lower bounds of Theorem 1.1(b).
--
--   Differences from the source:
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
--   - encoding: last layer of MPJ_k maps into {0, 1} → `Bool`; reason: relabelling
--   - encoding: success probability under µ_bool → `successMuBool`: number of correct tuples (a_1, π_2, …, π_{k−1}, F_k) divided by n·(n!)^{k−2}·2^n; reason: uniform law on a finite set
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 13 (PDF 15), Corollary 5.2; proof App. A.4.1, p. 36 (PDF 38)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem corollary_5_2 (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    (∀ (M : Fin (k - 1) → ℕ) (P : DetProtocol n k .bool M),
      successMuBool P ≤
        1 / 2 + Real.sqrt (((k : ℝ) - 3 / 2) * (totalComm M : ℝ) * Real.log 2 / (n : ℝ))) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
      ∀ (M : Fin (k - 1) → ℕ) (R : RandProtocol n k .bool M), R.IsEpsError ε →
        (1 / 2 - ε) ^ 2 * (n : ℝ) / (((k : ℝ) - 3 / 2) * Real.log 2) ≤ (totalComm M : ℝ) ∧
        (1 / 2 - ε) ^ 2 * (n : ℝ) / (((k : ℝ) - 1) * ((k : ℝ) - 3 / 2) * Real.log 2) ≤
          (maxComm M : ℝ)) := by sorry

end ConservativePJ.ManyPlayers
