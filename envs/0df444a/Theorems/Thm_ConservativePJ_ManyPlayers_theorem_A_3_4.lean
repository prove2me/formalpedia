-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_theorem_A_3_4
-- name    : ConservativePJ.ManyPlayers.theorem_A_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:57.854265+00:00
-- url     : https://prove2.me/theorems/075b708a-0632-48a7-98fa-2a331bb2974f
-- title:
--   Theorem A.3.4 — randomized upper bounds for $\mathrm{MPJ}_k$: $B_\varepsilon\le C_\varepsilon(1+n/k^2)$, $T_\varepsilon\le C_\varepsilon(n/k+\sqrt n)$
-- statement:
--   **Upper bounds for $\mathrm{MPJ}_k$.** For every $0<\varepsilon<1/2$ there is a constant $C_\varepsilon$ such that for all $n\ge2$ and $k\ge2$
--   $$B_\varepsilon(\mathrm{MPJ}_k)\le C_\varepsilon\Big(1+\frac n{k^2}\Big),\qquad T_\varepsilon(\mathrm{MPJ}_k)\le C_\varepsilon\Big(\frac nk+\sqrt n\Big),$$
--   and one public-coin conservative $\varepsilon$-error protocol for $\mathrm{MPJ}_k$ achieves both bounds.
--
--   It is the randomized starting point of the deterministic protocols for $\mathrm{MPJ}_k$ in Theorem 4.4(b).
--
--   Differences from the source:
--   - encoding: last layer of MPJ_k maps into {0, 1} → `Bool`; reason: relabelling
--   - encoding: B_ε, T_ε = least maximum / total communication of an ε-error protocol → `Bε n k pb ε`, `Tε n k pb ε` = `sInf` over ℕ of the costs of ε-error `RandProtocol`s; reason: the set is nonempty for n ≥ 1, k ≥ 2 (Player 1 lists f_k ∘ ⋯ ∘ f_2), so `sInf` is its least element
--   - reading: "there is a constant C_ε" → `∃ C : ℝ` chosen after ε and before n, k; reason: explicit quantifier form
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 24 (PDF 26), Theorem A.3.4 (App. A.3.3); proof p. 24 (PDF 26)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem theorem_A_3_4 :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, ∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
      (Bε n k .bool ε : ℝ) ≤ C * (1 + (n : ℝ) / (k : ℝ) ^ 2) ∧
      (Tε n k .bool ε : ℝ) ≤ C * ((n : ℝ) / (k : ℝ) + Real.sqrt n) ∧
      ∃ (M : Fin (k - 1) → ℕ) (R : RandProtocol n k .bool M), R.IsEpsError ε ∧
        (maxComm M : ℝ) ≤ C * (1 + (n : ℝ) / (k : ℝ) ^ 2) ∧
        (totalComm M : ℝ) ≤ C * ((n : ℝ) / (k : ℝ) + Real.sqrt n) := by sorry

end ConservativePJ.ManyPlayers
