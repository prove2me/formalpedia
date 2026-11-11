-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_lemma_A_3_9
-- name    : ConservativePJ.ManyPlayers.lemma_A_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:46.635122+00:00
-- url     : https://prove2.me/theorems/44a601df-2ad1-48ad-bcff-cb574988e611
-- title:
--   Lemma A.3.9 — lowering the error from $1/3$ to $1/(2d)$ with fewer than $64\sqrt d$ added players
-- statement:
--   **Lowering the error.** Let $n\ge2$, $m\ge2$, $1\le w\le n$, $d=\lceil n/w\rceil$, and fix a partition of $[n]$ into $w$ parts of size at most $d$. Let $P_0$ be a public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_m$ (resp. $\mathrm{MPJ}_m$) whose error probability is at most $1/3$ on every input, with maximum communication $B_0$ and total communication $T_0$. Then for some integer $0\le u<64\sqrt d$ there is a public-coin conservative protocol for $\widehat{\mathrm{MPJ}}_{m+u}$ (resp. $\mathrm{MPJ}_{m+u}$) whose error probability is at most $1/(2d)$ on every input, with
--   $$\text{maximum communication}\le\max\{B_0+1,\,w+1\},\qquad \text{total communication}\le T_0+u(w+1).$$
--   If the first message of $P_0$ has at most $w$ bits and its other messages before the output have at most $w+1$ bits each, then the new protocol has the same property.
--
--   This is the first half of the derandomization of Theorem 4.4; Lemma A.3.2 is the second.
--
--   Differences from the source:
--   - encoding: "The same holds with MPJ in place of MPĴ" (a separate sentence) → one statement quantified over `pb : Problem` (`.hat` = MPĴ, `.bool` = MPJ); reason: both cases at once; same content
--   - encoding: §4 standing assumption "we assume that n ≥ 2" (p. 9), not repeated in the lemma → hypothesis `2 ≤ n`; reason: the section's standing assumption made explicit
--   - encoding: a partition of [n] into w parts of size at most d → `G : Fin n → Fin w` surjective, every fibre of size ≤ d (`IsPartition G d`); reason: the parts are the fibres; same partitions
--   - encoding: d = ⌈n/w⌉ → `partBound n w = ⌈(n : ℝ)/w⌉₊`; reason: same number
--   - encoding: "first message has at most w bits, other messages before the output at most w + 1 bits each" → `LengthShape M w`: ℓ_1 ≤ w and ℓ_i ≤ w + 1 for 2 ≤ i ≤ m − 1; reason: same condition
--   - encoding: vertices [n] = {1, …, n}; Players 1, …, k → `Fin n`; the message of Player i + 1 has index i : Fin (k − 1), and Player k is the output map `out`; reason: relabelling; same inputs and the same speaking order
--   - encoding: message alphabet M_i fixed in advance, ℓ_i = ⌈log |M_i|⌉ → alphabet `Fin (M i)` with M i ≥ 1, ℓ_i = `Nat.clog 2 (M i)`; reason: every finite nonempty alphabet is in bijection with Fin |M_i|, and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1
--   - encoding: protocol with public and private coins (or public coins); error/success probability over the coins → `RandProtocol`: finitely many deterministic conservative protocols with the common alphabets, with real weights ≥ 0 summing to 1 and independent of the input; reason: fixing all coins gives a deterministic conservative protocol with the same alphabets (Lemma 2.3), and there are finitely many of them, so every coin space induces such a mixture with the same error on every input; every mixture is a public-coin protocol
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 31 (PDF 33), Lemma A.3.9 (App. A.3.6); proof pp. 31–32 (PDF 33–34)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_Protocol

namespace ConservativePJ.ManyPlayers

theorem lemma_A_3_9 (pb : Problem) (n m w : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (G : Fin n → Fin w) (hG : IsPartition G (partBound n w))
    (M0 : Fin (m - 1) → ℕ) (P0 : RandProtocol n m pb M0)
    (hP0 : ∀ x, P0.errorProb x ≤ 1 / 3) :
    ∃ u : ℕ, (u : ℝ) < 64 * Real.sqrt (partBound n w : ℝ) ∧
      ∃ (M : Fin (m + u - 1) → ℕ) (P : RandProtocol n (m + u) pb M),
        (∀ x, P.errorProb x ≤ 1 / (2 * (partBound n w : ℝ))) ∧
        maxComm M ≤ max (maxComm M0 + 1) (w + 1) ∧
        totalComm M ≤ totalComm M0 + u * (w + 1) ∧
        (LengthShape M0 w → LengthShape M w) := by sorry

end ConservativePJ.ManyPlayers
