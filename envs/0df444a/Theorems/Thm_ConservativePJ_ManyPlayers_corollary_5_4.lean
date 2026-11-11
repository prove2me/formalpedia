-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_corollary_5_4
-- name    : ConservativePJ.ManyPlayers.corollary_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:53.360718+00:00
-- url     : https://prove2.me/theorems/e435aea1-cdd6-4737-9d93-3e889886a29a
-- title:
--   Corollary 5.4 — total communication of order $\sqrt n$ for any number of players
-- statement:
--   **Total communication for any number of players.** For all $n\ge2$ and $k\ge2$,
--   $$T_\varepsilon(\widehat{\mathrm{MPJ}}_k)\ge\Big(1-\varepsilon-\frac1n\Big)\sqrt{\frac n{\ln2}}\quad(0\le\varepsilon<1),\qquad T_\varepsilon(\mathrm{MPJ}_k)>\Big(\frac12-\varepsilon\Big)\sqrt{\frac n{\ln2}}\quad(0\le\varepsilon<1/2).$$
--
--   This is the $\sqrt n$ term of the lower bounds of Theorem 1.1(b).
--
--   Differences from the source:
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
--   - encoding: last layer of MPJ_k maps into {0, 1} → `Bool`; reason: relabelling
--   - encoding: B_ε, T_ε = least maximum / total communication of an ε-error protocol → `Bε n k pb ε`, `Tε n k pb ε` = `sInf` over ℕ of the costs of ε-error `RandProtocol`s; reason: the set is nonempty for n ≥ 1, k ≥ 2 (Player 1 lists f_k ∘ ⋯ ∘ f_2), so `sInf` is its least element
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 14 (PDF 16), Corollary 5.4; proof App. A.4.1, p. 37 (PDF 39)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem corollary_5_4 (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      (1 - ε - 1 / (n : ℝ)) * Real.sqrt ((n : ℝ) / Real.log 2) ≤ (Tε n k .hat ε : ℝ)) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
      (1 / 2 - ε) * Real.sqrt ((n : ℝ) / Real.log 2) < (Tε n k .bool ε : ℝ)) := by sorry

end ConservativePJ.ManyPlayers
