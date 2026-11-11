-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_5_3
-- name    : ConservativePJ.ManyPlayers.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:54.010457+00:00
-- url     : https://prove2.me/theorems/4cf046ea-f16e-48d1-913f-d5f88b03309b
-- title:
--   Lemma 5.3 — removing silent players: at most $T+1$ players remain, with the same coins and error
-- statement:
--   **Removing silent players.** Let $n\ge2$ and $k\ge2$, and let $P$ be a conservative protocol with public and private coins and total communication $T$. Suppose that $P$ is a protocol for $\widehat{\mathrm{MPJ}}_k$ with error at most $\varepsilon<1-1/n$ on every input, or a protocol for $\mathrm{MPJ}_k$ with error at most $\varepsilon<1/2$ on every input. Then there is a conservative protocol for $\widehat{\mathrm{MPJ}}_{k'}$, respectively $\mathrm{MPJ}_{k'}$, with
--   $$2\le k'\le T+1$$
--   players and the same coins, whose error is at most $\varepsilon$ on every input. Its message alphabets are those of the players of $P$ who send at least one bit before the output, in their order.
--
--   With Lemma 5.1 it gives the $\sqrt n$ lower bound for any number of players (Corollary 5.4).
--
--   Differences from the source:
--   - encoding: "The same holds with MPJ in place of MPĴ" (a separate sentence) → one statement quantified over `pb : Problem` (`.hat` = MPĴ, `.bool` = MPJ); reason: both cases at once; same content
--   - encoding: "the same coins" → the new `RandProtocol` has the same index set `Fin N` and the same weights; reason: the coin distribution is the mixture's weights
--   - encoding: "Its message alphabets are those of the players of P who send at least one bit" → a strictly increasing `e : Fin (k′ − 1) → Fin (k − 1)` onto the players with ℓ_i ≥ 1, and M′_i = M_{e(i)}; reason: same alphabets in the same order
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 13 (PDF 15), Lemma 5.3; proof App. A.4.1, pp. 36–37 (PDF 38–39)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_5_3 (pb : Problem) (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (M : Fin (k - 1) → ℕ) (P : RandProtocol n k pb M) (ε : ℝ)
    (hε : (pb = .hat ∧ ε < 1 - 1 / (n : ℝ)) ∨ (pb = .bool ∧ ε < 1 / 2))
    (herr : P.IsEpsError ε) :
    ∃ k' : ℕ, 2 ≤ k' ∧ k' ≤ totalComm M + 1 ∧
      ∃ (M' : Fin (k' - 1) → ℕ) (P' : RandProtocol n k' pb M') (hN : P'.N = P.N),
        (∀ r : Fin P'.N, P'.weight r = P.weight (Fin.cast hN r)) ∧
        P'.IsEpsError ε ∧
        ∃ e : Fin (k' - 1) → Fin (k - 1), StrictMono e ∧
          Set.range e = {i : Fin (k - 1) | 1 ≤ msgLength (M i)} ∧ ∀ i, M' i = M (e i) := by sorry

end ConservativePJ.ManyPlayers
